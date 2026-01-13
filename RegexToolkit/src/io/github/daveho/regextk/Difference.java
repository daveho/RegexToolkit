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
import java.util.List;
import java.util.Set;

public class Difference implements FiniteAutomatonTransformer {
	private List<FiniteAutomaton> inputList;
	
	public Difference() {
		inputList = new ArrayList<FiniteAutomaton>();
	}

	@Override
	public void add(FiniteAutomaton input) {
		if (inputList.size() >= 2) {
			throw new IllegalArgumentException(this.getClass().getSimpleName() + " must have exactly two input automata");
		}
		inputList.add(input);
	}

	@Override
	public FiniteAutomaton execute(FiniteAutomatonTransformerMode mode) {
		if (inputList.size() != 2) {
			throw new IllegalArgumentException(this.getClass().getSimpleName() + " must have exactly two input automata");
		}
		
		Set<Character> universalAlphabet = FiniteAutomatonUtil.getUniversalAlphabet(inputList);
		
		// A - B = A ∩ 'B
		// i.e., A minus B is the intersection of A with B's complement
		
		Complement makeBComplement = new Complement();
		makeBComplement.add(inputList.get(1));
		makeBComplement.setAlphabet(universalAlphabet);
		FiniteAutomaton bComplement = makeBComplement.execute(mode);
		
		Intersection makeIntersection = new Intersection();
		makeIntersection.add(inputList.get(0));
		makeIntersection.add(bComplement);
		
		return makeIntersection.execute(mode);
	}

}
