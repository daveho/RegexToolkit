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
 * Represents a State of a FiniteAutomaton.
 * Note that States should not be created directly.
 * Instead, call the {@link FiniteAutomaton#createState()} method.
 */
public class State implements Comparable<State>, Cloneable {
	private int number;
	private boolean start;
	private boolean accepting;

	/**
	 * Constructor.
	 * 
	 * @param number state number for the new State
	 */
	public State(int number) {
		this.number = number;
		this.start = false;
		this.accepting = false;
	}
	
	/**
	 * @return the state number
	 */
	public int getNumber() {
		return number;
	}
	
	/**
	 * Add given amount to this State's state number.
	 * This is useful when combining FiniteAutomata, to ensure
	 * that the state numbers don't conflict.
	 * 
	 * @param add the amount to add to this State's state number
	 */
	public void addToNumber(int add) {
		number += add;
	}
	
	/**
	 * Set whether or not this State is a start state.
	 * 
	 * @param isStart true if this State should be a start state,
	 *                false otherwise
	 */
	public void setStart(boolean isStart) {
		start = isStart;
	}
	
	/**
	 * Set whether or not this State is an accepting state.
	 * 
	 * @param isAccepting true if this State should be an accepting state,
	 *                    false otherwise
	 */
	public void setAccepting(boolean isAccepting) {
		this.accepting = isAccepting;
	}

	/**
	 * @return true if this State is a start state, false otherwise
	 */
	public boolean isStart() {
		return start;
	}
	
	/**
	 * @return true if this State is an accepting State, false otherwise
	 */
	public boolean isAccepting() {
		return accepting;
	}
	
	@Override
	public String toString() {
		return "state " + number;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (obj == null || obj.getClass() != this.getClass()) {
			return false;
		}
		State other = (State) obj;
		return this.number == other.number;
	}
	
	@Override
	public int hashCode() {
		return number;
	}
	
	@Override
	public int compareTo(State other) {
		if (number < other.number) {
			return -1;
		} else if (number > other.number) {
			return 1;
		} else {
			return 0;
		}
	}
	
	@Override
	public State clone() {
		State dup;
		try {
			dup = (State)super.clone();
		} catch (CloneNotSupportedException e) {
			throw new IllegalStateException("not possible");
		}
		dup.number = this.number;
		dup.start = this.start;
		dup.accepting = this.accepting;
		return dup;
	}
}
