// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013,2017 David H. Hovemeyer <david.hovemeyer@gmail.com>
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
// 
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
// SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

package edu.ycp.cs.dh.regextk;

import java.text.CharacterIterator;

/**
 * Parse a regular expression and convert it to a nondeterministic finite automaton (NFA).
 */
public class ConvertRegexpToNFA {
	/*
	Grammar for simple regexps:

	s = symbol (character)
	ε = epsilon
	note that |, (, ), *, and + are all terminal symbols
	   (e.g., in the grammar, we're using "|" to mean the literal
	   "|" symbol, not as a shorthand for multiple productions
	   on the same nonterminal)

	Productions:

	R := E
	R := E|R        disjunction
	E := T
	E := TE         concatenation
	E := T
	T := F
	T := F*         repetition (0 or more)
	T := F+         repetition (1 or more)
	T := F?         optional (0 or 1)
	F := s          literal characters
	F := \s         escape sequence
	F := ε          epsilon
	F := (R)        grouping

	Supported escape sequences are:

	\d - digit (0-9)
	\a - alphabetic (A-Z, a-z)
	\x - hex digit (A-F, a-f, 0-9)
	\s - whitespace (' ', \t, \r, \n)
	
	Any escaped character other than the above allows matching
	of a literal character, even if it would otherwise be considered
	a metacharacter. E.g., \+ matches a literal "+" character.
	 */

	private static final boolean CHECK_NFA = true;
	private String regexp;
	private int pos;
	private int nextCh;

	private static final String DIGITS = "0123456789";
	private static final String ALPHA = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
	private static final String HEX_DIGITS = DIGITS + "ABCDEFabcdef";
	private static final String WHITESPACE = " \t\n\r";
	
	/**
	 * Constructor.
	 * 
	 * @param regexp a string containing a regular expression
	 */
	public ConvertRegexpToNFA(String regexp) {
		this.regexp = regexp;
		this.pos = 0;
		this.nextCh = -1;
	}

	/**
	 * Convert the regular expression (passed to the constructor)
	 * into an NFA.
	 * 
	 * @return the NFA which recognizes the language specified by the regular expression
	 */
	public FiniteAutomaton convertToNFA() {
		FiniteAutomaton fa = parseR();
		
		// Make sure that the entire regular expression was parsed.
		// This avoids situations, e.g., such as "a)*" being treated
		// as "a".
		if (!regexp.substring(pos).trim().isEmpty()) {
			throw new IllegalArgumentException("Regular expression had trailing symbols (mismatched parens?)");
		}
		
		return fa;
	}

	// Note: all intermediate NFAs are guaranteed to have a single start state
	// and a single accepting state.

	private FiniteAutomaton parseR() {
		// R := E
		// R := E|R        disjunction

		FiniteAutomaton e = parseE();

		int c = peek();
		if (c >= 0 && c == '|') {
			// disjunction

			// consume the "|"
			expect('|');

			// convert the right-hand side to an NFA
			FiniteAutomaton r = parseR();

			// build a big NFA to represent the disjunction
			Union union = new Union();
			union.add(e);
			union.add(r);
			FiniteAutomaton result = union.execute(FiniteAutomatonTransformerMode.DESTRUCTIVE); 

			// done
			return check(result);
		}

		return e;
	}

	private FiniteAutomaton parseE() {
		// E := T
		// E := TE         concatenation

		FiniteAutomaton t = parseT();

		int c = peek();

		if (c >= 0 && c != ')' && c != '|') {
			// concatenation

			FiniteAutomaton e = parseE();

			// create result automaton
			FiniteAutomaton result = new FiniteAutomaton();
			result.addAll(t);
			result.addAll(e);

			// create ε-transition connecting e's accepting state to r's start state
			result.createTransition(t.getUniqueAcceptingState(), e.getStartState(), FiniteAutomaton.EPSILON);
			t.getUniqueAcceptingState().setAccepting(false);
			e.getStartState().setStart(false);

			// done
			return check(result);
		}

		return t;
	}

	private FiniteAutomaton parseT() {
		// T := F
		// T := F*         repetition (0 or more)
		// T := F+         repetition (1 or more)
		// T := F?         optional (0 or 1)
		
		FiniteAutomaton f = parseF();
		
		int c = peek();
		if (c >= 0 && (c == '*' || c == '+')) {
			// repetition
			expect((char) c); // consume the * or +

			// Create result NFA with new start and accepting states
			FiniteAutomaton result = new FiniteAutomaton();
			State start = result.createState();
			start.setStart(true);
			State accepting = result.createState();
			accepting.setAccepting(true);

			// add ε-transitions from
			//   - start to accepting (only for '*', not for '+') and,
			//   - accepting to start state (both '*' and '+')
			// This allows 0 or more repetitions for '*', and 1 or more
			// repetitions for '+'.
			
			if (c == '*') {
				result.createTransition(start, accepting, FiniteAutomaton.EPSILON);
			}
			result.createTransition(accepting, start, FiniteAutomaton.EPSILON);

			// add states from orig NFA
			result.addAll(f);

			// add ε-transition from the new start state to the old start state
			result.createTransition(start, f.getStartState(), FiniteAutomaton.EPSILON);
			f.getStartState().setStart(false);

			// add ε-transition from the old accepting state to the new accepting state
			result.createTransition(f.getUniqueAcceptingState(), accepting, FiniteAutomaton.EPSILON);
			f.getUniqueAcceptingState().setAccepting(false);

			// done
			return check(result);
		} else if (c >= 0 && c == '?') {
			expect('?');
			
			// Create new start and accepting states, connected to/from
			// the original start and accepting states, and create an
			// epsilon transition from the new start state to the new
			// accepting state (allowing 0 occurrences of strings accepted
			// by the original FA.)
			State start = f.getStartState();
			State accept = f.getUniqueAcceptingState();
			State newStart = f.createState();
			State newAccept = f.createState();
			f.createTransition(newStart, start, FiniteAutomaton.EPSILON);     // allow 1 occurrence
			f.createTransition(accept, newAccept, FiniteAutomaton.EPSILON);   // as above
			start.setStart(false);
			newStart.setStart(true);
			accept.setAccepting(false);
			newAccept.setAccepting(true);
			f.createTransition(newStart, newAccept, FiniteAutomaton.EPSILON); // allow 0 occurrences
			
			return f;
		}
		
		// No operator (*+?) was applied, so just return whatever parseF() returned
		return f;
	}

	private FiniteAutomaton parseF() {
		// F := s          literal characters
		// F := ε          epsilon
		// F := (R)        grouping

		int c = next();

		if (c == '(') {
			// grouping
			FiniteAutomaton r = parseR();
			expect(')');
			return r;
		} else {
			// literal character or ε
			FiniteAutomaton result = new FiniteAutomaton();
			State start = result.createState();
			start.setStart(true);
			State accepting = result.createState();
			accepting.setAccepting(true);

			if (c == '\\') {
				// Handle escape sequence
				
				int nextC = next();
				
				switch (nextC) {
				case 'd':
					addTransitions(result, start, accepting, DIGITS);
					break;
				case 'a':
					addTransitions(result, start, accepting, ALPHA);
					break;
				case 'x':
					addTransitions(result, start, accepting, HEX_DIGITS);
					break;
				case 's':
					addTransitions(result, start, accepting, WHITESPACE);
					break;
				default:
					result.createTransition(start, accepting, (char) nextC);
				}
			} else {
				// match literal character or epsilon
				result.createTransition(start, accepting, c == 'ε' ? FiniteAutomaton.EPSILON : (char)c);
			}

			return check(result);
		}
	}

	private void addTransitions(FiniteAutomaton result, State start, State accepting, String symbols) {
		for (int i = 0; i < symbols.length(); ++i) {
			result.createTransition(start, accepting, symbols.charAt(i));
		}
	}

	private FiniteAutomaton check(FiniteAutomaton result) {
		if (CHECK_NFA) {
			result.getStartState();
			result.getUniqueAcceptingState();
		}
		return result;
	}

	private int peek() {
		while (this.nextCh < 0 && pos < regexp.length()) {
			int nextCh = regexp.charAt(pos++);
			
			// It's only a "valid" character if it isn't a space character
			if (!Character.isSpaceChar(nextCh)) {
				this.nextCh = convert(nextCh);
				break;
			}
		}
		
		return this.nextCh;
	}

	private int convert(int c) {
		return c == 'e' ? FiniteAutomaton.EPSILON : c;
	}

	private int next() {
		int c = peek();
		if (c < 0) {
			throw new IllegalArgumentException("regexp ended unexpectedly");
		}
		nextCh = -1;
		return c;
	}

	private void expect(int c) {
		int n = next();
		if (n != c) {
			throw new IllegalArgumentException("regexp parse error: expected " + ((char)c) + ", saw " + ((char)n));
		}
	}
}
