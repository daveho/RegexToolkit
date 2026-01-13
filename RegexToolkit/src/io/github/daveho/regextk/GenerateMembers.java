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
import java.util.LinkedList;
import java.util.List;
import java.util.TreeMap;

/**
 * Generate some members of the language recognized by a FiniteAutomaton.
 * The automaton must be deterministic.
 */
public class GenerateMembers {
	/**
	 * Maximum number of times we allow any state to be visited
	 * on any specific path.
	 */
	private static final int MAX_STATE_VISITS = 2;
	
	private FiniteAutomaton fa;
	private List<String> resultList;
	
	/**
	 * Constructor.
	 * 
	 * @param fa a FiniteAutomaton
	 */
	public GenerateMembers(FiniteAutomaton fa) {
		if (!FiniteAutomatonUtil.isDeterministic(fa)) {
			throw new IllegalArgumentException(this.getClass().getSimpleName() + " only works with DFAs");
		}
		this.fa = fa;
		this.resultList = new LinkedList<String>();
	}
	
	private static class Item {
		private String string;
		private State state;
		private TreeMap<State, Integer> timesVisitedMap;
		
		public Item(String string, State state) {
			this.string = string;
			this.state = state;
			timesVisitedMap = new TreeMap<State, Integer>();
		}
		
		public String getString() {
			return string;
		}
		
		public State getState() {
			return state;
		}
		
		public void visit() {
			Integer count = timesVisitedMap.get(state);
			if (count == null) {
				count = 0;
			}
			timesVisitedMap.put(state, count + 1);
		}
		
		public int numTimesVisited(State s) {
			Integer count = timesVisitedMap.get(s);
			return count == null ? 0 : count;
		}

		public Item follow(Transition t) {
			Item next = new Item(string + t.getSymbol(), t.getToState());
			next.timesVisitedMap.putAll(timesVisitedMap);
			return next;
		}
	}
	
	/**
	 * Find members of the language recognized by the FiniteAutomaton.
	 * 
	 * @param maxStrings the maximum number of strings to find
	 */
	public void execute(int maxStrings) {
		LinkedList<Item> workList = new LinkedList<Item>();
		
		Item seed = new Item("", fa.getStartState());
		workList.add(seed);
		
		while (!workList.isEmpty() && resultList.size() < maxStrings) {
			Item item = workList.removeFirst();
			item.visit();
			
			if (item.getState().isAccepting()) {
				resultList.add(item.getString());
			}
			
			for (Transition t : fa.getTransitions(item.getState())) {
				if (item.numTimesVisited(t.getToState()) < MAX_STATE_VISITS) {
					workList.addLast(item.follow(t));
				}
			}
		}
	}
	
	/**
	 * Get the list of member strings found by the previous
	 * call to execute().
	 * 
	 * @return list of member strings
	 */
	public List<String> getResultList() {
		return Collections.unmodifiableList(resultList);
	}
}
