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
import java.util.TreeSet;

public class RecognizesNonEmptyLanguage {
	public boolean execute(FiniteAutomaton fa) {
		// If any path from the start state leads to an accepting state,
		// then the automaton accepts at least one string.
		
		LinkedList<State> workList = new LinkedList<State>();
		Set<State> seen = new TreeSet<State>();
		
		workList.add(fa.getStartState());
		
		while (!workList.isEmpty()) {
			State s = workList.removeFirst();
			seen.add(s);
			
			if (s.isAccepting()) {
				return true;
			}
			
			for (Transition t : fa.getTransitions(s)) {
				if (!seen.contains(t.getToState())) {
					workList.addLast(t.getToState());
				}
			}
		}
		
		return false;
	}
}
