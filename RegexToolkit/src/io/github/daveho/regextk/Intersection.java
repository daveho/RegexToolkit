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
import java.util.List;
import java.util.Set;

/**
 * Create a FiniteAutomaton that recognizes the intersection of
 * the languages recognized by given input automata.
 * 
 * Result returned will be deterministic.
 */
public class Intersection extends MultipleInputFiniteAutomatonTransformer implements FiniteAutomatonTransformer {

	@Override
	public FiniteAutomaton execute(FiniteAutomatonTransformerMode mode) {
		List<FiniteAutomaton> inputList = getInputList();
		
		// determine the overall alphabet - this determines the universe of
		// possible input strings
		Set<Character> universalAlphabet = FiniteAutomatonUtil.getUniversalAlphabet(inputList);
		
		// A ∩ B = '('A ∪ 'B)
		// i.e., the intersection of A and B is the complement of the union of the complements of A and B
		
		// complement all input automata
		List<FiniteAutomaton> complementList = new LinkedList<FiniteAutomaton>();
		for (FiniteAutomaton input : inputList) {
			Complement makeComplement = new Complement();
			makeComplement.add(input);
			makeComplement.setAlphabet(universalAlphabet);
			complementList.add(makeComplement.execute(mode));
		}
		
		// create one automaton that recognizes the union of the complements of all input automata
		Union makeUnion = new Union();
		for (FiniteAutomaton comp : complementList) {
			makeUnion.add(comp);
		}
		FiniteAutomaton unionOfComplements = makeUnion.execute(mode);
		
		// the result is the complement of the union of the complements
		Complement makeResult = new Complement();
		makeResult.add(unionOfComplements);
		makeResult.setAlphabet(universalAlphabet);
		return makeResult.execute(mode);
	}

}
