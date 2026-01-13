// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013, David H. Hovemeyer <david.hovemeyer@gmail.com>
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

package io.github.daveho.regextk;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * Some utility static methods that are useful for working with Automata.
 * Contains methods which are helpful when working with sets of
 * states in the simulation of an NFA.  Also contains methods
 * for transforming FiniteAutomata and performing set operations.
 */
public abstract class FiniteAutomatonUtil {

	// prevent instantiation
	private FiniteAutomatonUtil() {
	}
	
	/**
	 * Compute set of States directly reached by following transitions
	 * from given current set of States on given input symbol.
	 * Note that this method finds directly-reachable states, not the closure
	 * (following epsilon transitions).  You can call the {@link #closure(FiniteAutomaton, StateSet)}
	 * method to get the closure of the result of this method.
	 * 
	 * @param fa      an FiniteAutomaton
	 * @param current set of States
	 * @param c       input symbols
	 * @return Set of States directly reached by consuming the input symbol 
	 */
	public static StateSet followAll(FiniteAutomaton fa, StateSet current, char c) {
		StateSet result = new StateSet();
		for (State s : current.getStates()) {
			for (Transition t : fa.getTransitions(s)) {
				if (t.getSymbol() == c) {
					result.add(t.getToState());
				}
			}
		}
		return result;
	}

	/**
	 * Compute the closure of given set of States by following
	 * epsilon transitions.
	 * 
	 * @param fa      an FiniteAutomaton
	 * @param current set of States
	 * @return        the closure of the set of States
	 */
	public static StateSet closure(FiniteAutomaton fa, StateSet current) {
		StateSet result = new StateSet();
		LinkedList<State> work = new LinkedList<State>(current.getStates());
		
		while (!work.isEmpty()) {
			State s = work.removeFirst();
			result.add(s);
			List<Transition> transitions = fa.getTransitions(s);
			for (Transition t : transitions) {
				if (t.getSymbol() == FiniteAutomaton.EPSILON) {
					if (result.add(t.getToState())) {
						work.add(t.getToState());
					}
				}
			}
		}
		
		return result;
	}

	/**
	 * Return true if the given set of States contains an accepting
	 * state, false otherwise.
	 * 
	 * @param current a set of States
	 * @return true if set of States contains an accepting state, false otherwise
	 */
	public static boolean containsAcceptingState(StateSet current) {
		for (State s : current.getStates()) {
			if (s.isAccepting()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Get a Set containing the alphabet of symbols (characters)
	 * used in transitions in given FiniteAutomaton.
	 * Epsilon transitions are ignored.
	 * 
	 * @param a an FiniteAutomaton
	 * @return alphabet (set of characters) used by the FiniteAutomaton
	 */
	public static Set<Character> getAlphabet(FiniteAutomaton a) {
		TreeSet<Character> result = new TreeSet<Character>(); 
		for (Transition t : a.getAllTransitions()) {
			if (t.getSymbol() != FiniteAutomaton.EPSILON) {
				result.add(t.getSymbol());
			}
		}
		return result;
	}

	/**
	 * Determine whether or not given FiniteAutomaton is deterministic.
	 * 
	 * @param fa a FiniteAutomaton
	 * @return true if the FiniteAutomaton is deterministic, false if it is nondeterministic
	 */
	public static boolean isDeterministic(FiniteAutomaton fa) {
		// if there are any epsilon transitions, it's nondeterministic
		for (Transition t : fa.getAllTransitions()) {
			if (t.getSymbol() == FiniteAutomaton.EPSILON) {
				return false;
			}
		}
		
		// If any state has multiple transitions on same input symbol,
		// it's nondeterministic
		for (State s : fa.getStates()) {
			Set<Character> seen = new TreeSet<Character>();
			for (Transition t : fa.getTransitions(s)) {
				if (seen.contains(t.getSymbol())) {
					// this is a second transition on the same input symbol
					return false;
				}
				seen.add(t.getSymbol());
			}
		}
		
		// the automaton has no nondeterministic features
		return true;
	}

	/**
	 * Get the union of the alphabets of a collection of FiniteAutomata. 
	 * 
	 * @param inputList a Collection of FiniteAutomata
	 * @return union of the alphabets of the collection of FiniteAutomata
	 */
	public static Set<Character> getUniversalAlphabet(Collection<FiniteAutomaton> inputList) {
		Set<Character> universalAlphabet;
		universalAlphabet = new TreeSet<Character>();
		for (FiniteAutomaton input : inputList) {
			universalAlphabet.addAll(getAlphabet(input));
		}
		return universalAlphabet;
	}

	/**
	 * Convert a regular expression to an nondeterministic FiniteAutomaton.
	 * 
	 * @param regexp a regular expression
	 * @return a FiniteAutomata recognizing the language generated by the regular expression
	 */
	public static FiniteAutomaton convertToNFA(String regexp) {
		ConvertRegexpToNFA convert = new ConvertRegexpToNFA(regexp);
		return convert.convertToNFA();
	}

	/**
	 * Return a FiniteAutomaton that recognizes the difference of the
	 * languages recognized by two input FiniteAutomata.
	 * 
	 * @param a FiniteAutomaton A
	 * @param b FiniteAutomaton B
	 * @return a FiniteAutomaton recognizing A - B
	 */
	public static FiniteAutomaton difference(FiniteAutomaton a, FiniteAutomaton b) {
		Difference diff = new Difference();
		diff.add(a);
		diff.add(b);
		return diff.execute(FiniteAutomatonTransformerMode.NONDESTRUCTIVE);
	}

	/**
	 * Determine whether given FiniteAutomaton recognizes a non-empty language.
	 * 
	 * @param fa  a FiniteAutomaton
	 * @return true if the automaton recognizes a non-empty language, false otherwise
	 */
	public static boolean recognizesNonEmptyLanguage(FiniteAutomaton fa) {
		RecognizesNonEmptyLanguage r = new RecognizesNonEmptyLanguage();
		return r.execute(fa);
	}

	/**
	 * Convert given NFA to DFA.
	 * 
	 * @param nfa an NFA
	 * @return an equivalent DFA
	 */
	public static FiniteAutomaton convertToDFA(FiniteAutomaton nfa) {
		ConvertNFAToDFA converter = new ConvertNFAToDFA();
		converter.add(nfa);
		return converter.execute(FiniteAutomatonTransformerMode.NONDESTRUCTIVE);
	}
}
