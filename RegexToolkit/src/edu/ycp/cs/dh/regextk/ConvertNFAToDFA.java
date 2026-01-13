// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013,2026 David H. Hovemeyer <david.hovemeyer@gmail.com>
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

import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * Build a deterministic FiniteAutomaton that recognizes the same
 * language as a given nondeterministic FiniteAutomaton.
 */
public class ConvertNFAToDFA extends SingleInputFiniteAutomatonTransformer implements FiniteAutomatonTransformer {
	private FiniteAutomaton nfa;
	private Map<StateSet, State> nfaToDfaStateMap;
	private FiniteAutomaton dfa;

	/**
	 * Constructor.
	 * 
	 * @param nfa the nondeterministic FiniteAutomaton to be translated into
	 *            a deterministic FiniteAutomaton
	 */
	public ConvertNFAToDFA() {
		this.nfaToDfaStateMap = new TreeMap<StateSet, State>();
		this.dfa = new FiniteAutomaton();
	}
	
	@Override
	public FiniteAutomaton execute(FiniteAutomatonTransformerMode mode) {
		// This transformer is always nondestructive
		nfa = getInput();
		return convertToDFA();
	}
	
	private FiniteAutomaton convertToDFA() {
		Set<Character> alphabet = FiniteAutomatonUtil.getAlphabet(nfa);
		Set<StateSet> added = new TreeSet<StateSet>();
		
		// create the DFA start state
		State dfaStart = dfa.createState();
		dfaStart.setStart(true);
		
		// map closure of NFA start state to the DFA start state
		StateSet nfaStart = new StateSet();
		nfaStart.add(nfa.getStartState());
		nfaStart = FiniteAutomatonUtil.closure(nfa, nfaStart);
		nfaToDfaStateMap.put(nfaStart, dfaStart);
		
		// Seed work list
		LinkedList<StateSet> workList = new LinkedList<StateSet>();
		workList.add(nfaStart);
		
		// Main loop
		while (!workList.isEmpty()) {
			StateSet nfaStates = workList.removeLast();
			added.add(nfaStates);
			
			State dfaState = getEquivalentDFAState(nfaStates);
			
			for (char c : alphabet) {
				StateSet reachableNfaStates = FiniteAutomatonUtil.closure(nfa, FiniteAutomatonUtil.followAll(nfa, nfaStates, c));
				if (!reachableNfaStates.isEmpty()) {
					State targetDfaState = getEquivalentDFAState(reachableNfaStates);
					dfa.createTransition(dfaState, targetDfaState, c);
					if (!added.contains(reachableNfaStates)) {
						added.add(reachableNfaStates);
						workList.add(reachableNfaStates);
					}
				}
			}
		}
		
		// Determine which DFA states are accepting states
		for (Map.Entry<StateSet, State> e : nfaToDfaStateMap.entrySet()) {
			StateSet nfaStates = e.getKey();
			State dfaState = e.getValue();
			if (FiniteAutomatonUtil.containsAcceptingState(nfaStates)) {
				dfaState.setAccepting(true);
			}
		}
		
		return dfa;
	}

	private State getEquivalentDFAState(StateSet nfaStates) {
		State dfaState = nfaToDfaStateMap.get(nfaStates);
		if (dfaState == null) {
			dfaState = dfa.createState();
			nfaToDfaStateMap.put(nfaStates, dfaState);
		}
		return dfaState;
	}
	
	/**
	 * Get the NFA {@link StateSet} corresponding to the given DFA state.
	 * 
	 * @param dfaState a DFA state
	 * @return the NFA {@link StateSet} corresponding to the DFA state
	 */
	public StateSet getNFAStateSetForDFAState(State dfaState) {
		for (Map.Entry<StateSet, State> e : nfaToDfaStateMap.entrySet()) {
			if (e.getValue() == dfaState)
				return e.getKey();
		}
		throw new IllegalArgumentException("DFA state not found");
	}
}
