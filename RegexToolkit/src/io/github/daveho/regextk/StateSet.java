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

import java.util.Collections;
import java.util.Iterator;
import java.util.SortedSet;
import java.util.TreeSet;

/**
 * A StateSet represents a set of states in an FiniteAutomaton.
 * It is useful for simulating the behavior of an NFA
 * (which, due to nondeterminism, can be in multiple states
 * simultaneously.)
 * 
 * This class implements the Comparable interface,
 * and defines hashCode and equals methods, so instances of
 * StateSet may be used as keys in TreeSets/TreeMaps
 * and HashSets/HashMaps.
 */
public class StateSet implements Comparable<StateSet> {
	private TreeSet<State> states;

	/**
	 * Constructor.  Initializes an empty set of States.
	 */
	public StateSet() {
		states = new TreeSet<State>();
	}
	
	/**
	 * @return the Set of States in this StateSet
	 */
	public SortedSet<State> getStates() {
		return Collections.unmodifiableSortedSet(states);
	}

	/**
	 * Add a State to the StateSet.
	 * 
	 * @param s the State to add
	 * @return true if the State is being added to the StateSet for the first time,
	 *         false if the State was already a member of this StateSet
	 */
	public boolean add(State s) {
		return states.add(s);
	}

	/**
	 * @return true if the StateSet contains no states, false otherwise
	 */
	public boolean isEmpty() {
		return states.isEmpty();
	}
	
	@Override
	public int compareTo(StateSet o) {
		// this is a lexicographical comparison
		
		Iterator<State> i = this.states.iterator();
		Iterator<State> j = o.states.iterator();
		
		while (i.hasNext() && j.hasNext()) {
			State lhs = i.next();
			State rhs = j.next();
			
			int cmp = lhs.compareTo(rhs);
			if (cmp != 0) {
				return cmp;
			}
		}
		
		if (!i.hasNext() && !j.hasNext()) {
			return 0;
		}
		return !i.hasNext() ? -1 : 1;
	}
	
	@Override
	public int hashCode() {
		int code = 0;
		for (State s : states) {
			code *= 7;
			code += s.hashCode();
		}
		return code;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (obj == null || obj.getClass() != this.getClass()) {
			return false;
		}
		StateSet other = (StateSet) obj;
		return this.states.equals(other.states);
	}
	
	@Override
	public String toString() {
		StringBuilder buf = new StringBuilder();
		boolean first = true;
		buf.append("{");
		for (State member : states) {
			if (first)
				first = false;
			else
				buf.append(",");
			buf.append(String.valueOf(member.getNumber()));
		}
		buf.append("}");
		return buf.toString();
	}
}
