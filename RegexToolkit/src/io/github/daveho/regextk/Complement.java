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

import java.util.Set;

/**
 * Transform a FiniteAutomaton into one that accepts the complement
 * of the language accepted by the original.
 * 
 * The resulting automaton will be deterministic, even if the original
 * automaton is not.
 */
public class Complement extends SingleInputFiniteAutomatonTransformer implements FiniteAutomatonTransformer {
	private Set<Character> alphabet;
	
	/**
	 * Specify the alphabet.
	 * This is important for creating an automaton to recognize the
	 * complement of a language, since it defines the universal set
	 * (all possible input strings) that the complement is
	 * relative to.
	 * 
	 * @param alphabet the alphabet
	 */
	public void setAlphabet(Set<Character> alphabet) {
		this.alphabet = alphabet;
	}

	@Override
	public FiniteAutomaton execute(FiniteAutomatonTransformerMode mode) {
		FiniteAutomaton fa = getInput();
		
		if (!FiniteAutomatonUtil.isDeterministic(fa)) {
			// input automaton is nondeterministic - convert it to a DFA.
			// this will create a new FA.
			ConvertNFAToDFA makeDFA = new ConvertNFAToDFA();
			makeDFA.add(fa);
			fa = makeDFA.execute(FiniteAutomatonTransformerMode.NONDESTRUCTIVE);
		}
		
		if (alphabet == null) {
			alphabet = FiniteAutomatonUtil.getAlphabet(fa);
		}
		
		// create an explicit reject state
		CreateExplicitRejectState createExplicitRejectState = new CreateExplicitRejectState();
		createExplicitRejectState.add(fa);
		createExplicitRejectState.setAlphabet(alphabet);
		fa = createExplicitRejectState.execute(mode);
		
		// this is a simple transformation: we just change every accepting state
		// to a nonaccepting state, and vice versa
		for (State s : fa.getStates()) {
			s.setAccepting(!s.isAccepting());
		}
		
		fa.getStartState(); // check
		
		return fa;
	}
}
