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

/**
 * Represents a transition in a FiniteAutomaton.
 * Note: do not create Transitions directly.  Instead, use the
 * {@link FiniteAutomaton#createTransition(State, State, char)} method.
 */
public class Transition implements Comparable<Transition> {
	private State fromState;
	private State toState;
	private char symbol;

	/**
	 * Constructor.
	 * 
	 * @param fromState the State the Transition starts from
	 * @param toState   the State the Transition goes to
	 * @param symbol    the symbol consumed by the Transition; {@link FiniteAutomaton#EPSILON} if
	 *                  the Transition does not consume a symbol
	 */
	public Transition(State fromState, State toState, char symbol) {
		if (fromState == null || toState == null) {
			throw new IllegalArgumentException();
		}
		this.fromState = fromState;
		this.toState = toState;
		this.symbol = symbol;
	}

	/**
	 * @return the State the Transition comes from
	 */
	public State getFromState() {
		return fromState;
	}
	
	/**
	 * @return the State the Transition goes to
	 */
	public State getToState() {
		return toState;
	}
	
	/**
	 * @return the symbol consumed by the Transition, or {@link FiniteAutomaton#EPSILON}
	 *         if the Transition does not consume a symbol
	 */
	public char getSymbol() {
		return symbol;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (obj == null || obj.getClass() != this.getClass()) {
			return false;
		}
		Transition other = (Transition) obj;
		return this.fromState.equals(other.fromState)
			&& this.toState.equals(other.toState)
			&& this.symbol == other.symbol;
	}
	
	@Override
	public int hashCode() {
		return fromState.hashCode() * 107 + toState.hashCode() * 37 + (int)symbol;
	}
	
	@Override
	public int compareTo(Transition o) {
		int cmp;
		
		cmp = fromState.compareTo(o.fromState);
		if (cmp != 0) {
			return cmp;
		}

		cmp = toState.compareTo(o.toState);
		if (cmp != 0) {
			return cmp;
		}
		
		if (symbol < o.symbol) {
			return -1;
		} else if (symbol > o.symbol) {
			return 1;
		} else {
			return 0;
		}
	}
	
	@Override
	public String toString() {
		return symbol + ": " + fromState.toString() + " -> " + toState.toString();
	}
}
