// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013,2014,2026 David H. Hovemeyer <david.hovemeyer@gmail.com>
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

import java.util.Set;

/**
 * Implementation of ExecuteFiniteAutomaton that works only with deterministic
 * finite automata, but should be very fast because it uses a table-driven
 * approach. Note that this class can also be used for just building a
 * transition table.
 */
public class ExecuteDFA implements ExecuteFiniteAutomaton {
	private int minCC;
	private int[][] table;
	private int startState;
	private boolean[] acceptingStates;
	private int rangeSize;
	
	@Override
	public void setAutomaton(FiniteAutomaton fa) {
		if (!FiniteAutomatonUtil.isDeterministic(fa)) {
			throw new IllegalArgumentException("ExecuteDFA can only be used with a deterministic finite automaton");
		}
		
		// build a lookup table listing, for each state, which other state (if any)
		// is reachable by following a transition on possible input symbols
		
		// find minimum and maximum character code used
		Set<Character> alphabet = FiniteAutomatonUtil.getAlphabet(fa);
		if (alphabet.isEmpty()) {
			// Special case: the automaton only accepts the empty string
			rangeSize = 0;
		} else {
			// find out the range of character codes used
			minCC = 65536;
			int maxCC = 0;
			for (char c : alphabet) {
				if (c < minCC) {
					minCC = c;
				}
				if (c > maxCC) {
					maxCC = c;
				}

			}
			this.rangeSize = (maxCC+1) - minCC;
		}
		
		// create the table and initialize it so that there are no valid transitions
		table = new int[fa.getNumStates()][rangeSize];
		for (int j = 0; j < fa.getNumStates(); j++) {
			for (int i = 0; i < rangeSize; i++) {
				table[j][i] = -1;
			}
		}
		
		// add all valid transitions to the table
		for (Transition t : fa.getAllTransitions()) {
			table[t.getFromState().getNumber()][t.getSymbol() - minCC] = t.getToState().getNumber();
		}
		
		// determine which state is the start state
		startState = fa.getStartState().getNumber();
		
		// build table recording which states are accepting states
		acceptingStates = new boolean[fa.getNumStates()];
		for (State s : fa.getStates()) {
			if (s.isAccepting()) {
				acceptingStates[s.getNumber()] = true;
			}
		}
	}
	
	/**
	 * Get the minimum character code used in the FA.
	 * 
	 * @return minimum character code
	 */
	public int getMinCC() {
		return minCC;
	}
	
	/**
	 * Get the size of the range of character codes,
	 * i.e., (maxCC - minCC) + 1. This is the number of elements
	 * in each row of the transition table.
	 * 
	 * @return the range size
	 */
	public int getRangeSize() {
		return rangeSize;
	}
	
	/**
	 * Get the transition table.
	 * The rows (first dimension) are indexed by DFA state number.
	 * The columns (second dimension) are indexed by offset of the
	 * character code from the minimum character code (accessed by
	 * calling {@link #getMinCC()}).
	 * 
	 * @return the transition table
	 */
	public int[][] getTable() {
		return table;
	}
	
	@Override
	public Answer execute(String s) {
		try {
			return doExecute(s);
		} catch (ArrayIndexOutOfBoundsException e) {
			// This can happen if a symbol not in the language's
			// predicted alphabet is used.
			return Answer.REJECT;
		}
	}

	// Execute "unsafely" by not checking whether symbols in the
	// String are in the automaton's predicted alphabet.
	public Answer doExecute(String s) {
		int state = startState;
		for (int i = 0; i < s.length(); i++) {
			char c = s.charAt(i);
			int next = table[state][((int)c) - minCC];
			if (next < 0) {
				return Answer.REJECT; // no transition on c
			}
			state = next;
		}
		return acceptingStates[state] ? Answer.ACCEPT : Answer.REJECT;
	}

}
