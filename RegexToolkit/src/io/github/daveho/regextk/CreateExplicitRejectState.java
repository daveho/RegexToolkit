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

import java.util.LinkedList;
import java.util.Set;

/**
 * FiniteAutomatonTransformer which creates an explicit "reject" state.
 * In each state of the original automaton, any "missing" transitions
 * (i.e., input symbols for which no explicit transition exists)
 * are created, leading to a "reject" state.
 * 
 * The resulting automaton has the same determinacy as the original one.
 */
public class CreateExplicitRejectState extends SingleInputFiniteAutomatonTransformer implements FiniteAutomatonTransformer {
	private Set<Character> alphabet;
	
	/**
	 * Specify the alphabet.
	 * 
	 * @param alphabet the alphabet
	 */
	public void setAlphabet(Set<Character> alphabet) {
		this.alphabet = alphabet;
	}
	
	@Override
	public FiniteAutomaton execute(FiniteAutomatonTransformerMode mode) {
		FiniteAutomaton fa = getInput();
		
		fa.getStartState();
		
		if (mode == FiniteAutomatonTransformerMode.NONDESTRUCTIVE) {
			fa = fa.clone();
		}
		
		State rejectState = null;
		
		if (alphabet == null) {
			alphabet = FiniteAutomatonUtil.getAlphabet(fa);
		}

		LinkedList<State> statesCopy = new LinkedList<State>();
		statesCopy.addAll(fa.getStates());
		
		for (State s : statesCopy) {
			for (Character sym : alphabet) {
				if (fa.getTransition(s, sym) == null) {
					// missing transition
					
					// create the reject state if not already created
					if (rejectState == null) {
						rejectState = fa.createState();
						for (Character c : alphabet) {
							fa.createTransition(rejectState, rejectState, c);
						}
					}
					
					// create an explicit transition leading to the reject state
					fa.createTransition(s, rejectState, sym);
				}
			}
		}
		
		return fa;
	}
}
