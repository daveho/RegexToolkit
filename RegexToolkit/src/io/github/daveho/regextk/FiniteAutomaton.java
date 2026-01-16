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

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * Represents a finite automaton (deterministic or nondeterministic).
 */
public class FiniteAutomaton implements Cloneable {
	/**
	 * Symbol used to label transitions that do not consume an input symbol.
	 */
	public static final char EPSILON = 'ε';

	private List<State> stateList;
	private List<Transition> transitionList;
	private Map<Integer, List<Transition>> stateToTransitionListMap;
	
	/**
	 * Constructor.
	 */
	public FiniteAutomaton() {
		stateList = new LinkedList<State>();
		transitionList = new LinkedList<Transition>();
		stateToTransitionListMap = new TreeMap<Integer, List<Transition>>();
	}
	
	/**
	 * Create a new State.
	 * The States are numbered in order of creation, starting at 0.
	 * 
	 * @return the new State
	 */
	public State createState() {
		State s = new State(stateList.size());
		stateList.add(s);
		stateToTransitionListMap.put(s.getNumber(), new ArrayList<Transition>());
		return s;
	}
	
	/**
	 * Create a Transition from one State to another State.
	 * Both States must be part of the FiniteAutomaton.
	 * 
	 * @param fromState the State that the Transition starts from
	 * @param toState   the State that the Transition goes to
	 * @param symbol    the symbol consumed by the Transition: EPSILON represents
	 *                  a Transition that does not consume a symbol
	 * @return the new Transition
	 */
	public Transition createTransition(State fromState, State toState, char symbol) {
		Transition t = new Transition(fromState, toState, symbol);
		transitionList.add(t);
		stateToTransitionListMap.get(fromState.getNumber()).add(t);
		return t;
	}
	
	/**
	 * Get the start State of the FiniteAutomaton.
	 * 
	 * @return the start State
	 */
	public State getStartState() {
		State start = null;
		for (State s : stateList) {
			if (s.isStart()) {
				if (start != null) {
					throw new IllegalStateException("Multiple start states: " + start + " and " + s);
				}
				start = s;
			}
		}
		if (start == null) {
			throw new IllegalStateException("No start state");
		}
		return start;
	}
	
	/**
	 * Get a List of all accepting (final) States of the FiniteAutomaton.
	 * 
	 * @return List of all accepting States
	 */
	public List<State> getAcceptingStates() {
		LinkedList<State> result = new LinkedList<State>();
		
		for (State s : stateList) {
			if (s.isAccepting()) {
				result.add(s);
			}
		}
		
		return result;
	}

	/**
	 * Add all states and transitions in given FiniteAutomaton to this automaton.
	 * The states of the given automaton are renumbered so that they
	 * don't conflict.
	 * 
	 * @param other another FiniteAutomaton, whose States and Transitions
	 *              will be added to this FiniteAutomaton
	 */
	public void addAll(FiniteAutomaton other) {
		other.addToStateNumbers(stateList.size());
		stateList.addAll(other.stateList);
		transitionList.addAll(other.transitionList);
		stateToTransitionListMap.putAll(other.stateToTransitionListMap);
	}
	
	private void addToStateNumbers(int add) {
		for (State s : stateList) {
			s.addToNumber(add);
		}
		
		// Fix stateToTransitionListMap, since the states have been renumbered
		TreeMap<Integer, List<Transition>> update = new TreeMap<Integer, List<Transition>>();
		for (Map.Entry<Integer, List<Transition>> entry : stateToTransitionListMap.entrySet()) {
			update.put(entry.getKey() + add, entry.getValue());
		}
		stateToTransitionListMap = update;
	}

	/**
	 * Get all transitions leading out of given State.
	 * 
	 * @param s a State
	 * @return  List of all transitions out of the State
	 */
	public List<Transition> getTransitions(State s) {
		return Collections.unmodifiableList(stateToTransitionListMap.get(s.getNumber()));
	}
	
	/**
	 * Get the Transition out of given state on given input symbol.
	 * Returns null if no such transition exists. 
	 * 
	 * @param s    a State in the FiniteAutomaton
	 * @param sym  an input symbol
	 * @return the Transition out of the state on the given symbol, or null if no such state exists
	 */
	public Transition getTransition(State s, char sym) {
		List<Transition> transitions = getTransitions(s);
		for (Transition t : transitions) {
			if (t.getSymbol() == sym) {
				return t;
			}
		}
		return null;
	}

	/**
	 * Get a List of all States in the FiniteAutomaton.
	 * 
	 * @return List of all States in the FiniteAutomaton
	 */
	public List<State> getStates() {
		return Collections.unmodifiableList(stateList);
	}

	/**
	 * Get a List of all Transitions in the FiniteAutomaton.
	 * 
	 * @return List of all Transitions in the FiniteAutomaton
	 */
	public List<Transition> getAllTransitions() {
		return Collections.unmodifiableList(transitionList);
	}

	/**
	 * @return number of States in the FiniteAutomaton
	 */
	public int getNumStates() {
		return stateList.size();
	}
	
	@Override
	public FiniteAutomaton clone() {
		FiniteAutomaton dup;
		try {
			dup = (FiniteAutomaton) super.clone();
			// Reinitialize the object so that it is in a "newly-constructed" state
			dup.stateList = new LinkedList<State>();
			dup.transitionList = new LinkedList<Transition>();
			dup.stateToTransitionListMap = new TreeMap<Integer, List<Transition>>();
		} catch (CloneNotSupportedException e) {
			throw new IllegalStateException("should't happen");
		}
		
		// create duplicate states
		Map<State, State> stateMap = new TreeMap<State, State>();
		for (State origState : this.stateList) {
			State dupState = dup.createState();
			dupState.setStart(origState.isStart());
			dupState.setAccepting(origState.isAccepting());
			
			stateMap.put(origState, dupState);
		}
		
		// create duplicate transitions
		for (Transition origTransition : this.transitionList) {
			State newFrom = stateMap.get(origTransition.getFromState());
			State newTo = stateMap.get(origTransition.getToState());
			dup.createTransition(newFrom, newTo, origTransition.getSymbol());
		}
		
		return dup;
	}

	/**
	 * Get the unique accepting state of this automaton.
	 * 
	 * @return the unique accepting state of this automaton
	 * @throws IllegalStateException if there is not a unique accepting state 
	 */
	public State getUniqueAcceptingState() {
		List<State> allAccepting = getAcceptingStates();
		if (allAccepting.size() != 1) {
			throw new IllegalStateException();
		}
		return allAccepting.get(0);
	}
}
