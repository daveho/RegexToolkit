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

import java.util.List;

/**
 * Create a FiniteAutomaton that recognizes the union of the languages
 * recognized by input FiniteAutomata.  The result will be nondeterministic.
 */
public class Union extends MultipleInputFiniteAutomatonTransformer implements FiniteAutomatonTransformer {
	@Override
	public FiniteAutomaton execute(FiniteAutomatonTransformerMode mode) {
		List<FiniteAutomaton> inputList = getInputList();
		
		FiniteAutomaton result = new FiniteAutomaton();
		State start = result.createState();
		start.setStart(true);
		State accepting = result.createState();
		accepting.setAccepting(true);

		for (FiniteAutomaton input : inputList) {
			// the input automaton must be transformed to have a unique accepting state
			MakeUniqueAcceptingState makeUniqueAcceptingState = new MakeUniqueAcceptingState();
			makeUniqueAcceptingState.add(input);
			input = makeUniqueAcceptingState.execute(mode);
			
			// add all states and transitions
			result.addAll(input);

			// add ε-transitions from the result start state to
			// the sub-automaton start state
			State subStart = input.getStartState();
			result.createTransition(start, subStart, FiniteAutomaton.EPSILON);
			subStart.setStart(false);

			// add ε-transitions from the sub-automaton accepting state
			// to the result accepting state
			State subAccepting = input.getUniqueAcceptingState();
			result.createTransition(subAccepting, accepting, FiniteAutomaton.EPSILON);
			subAccepting.setAccepting(false);
		}
		
		return result;
	}

}
