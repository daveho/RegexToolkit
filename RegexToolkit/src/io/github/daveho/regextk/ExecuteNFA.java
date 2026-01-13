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


/**
 * Implementation of ExecuteFiniteAutomaton that can be used with
 * nondeterministic finite automata.
 */
public class ExecuteNFA implements ExecuteFiniteAutomaton {
	private FiniteAutomaton fa;
	
	@Override
	public void setAutomaton(FiniteAutomaton fa) {
		this.fa = fa;
	}
	
	@Override
	public Answer execute(String s) {
		// compute the starting set of states
		StateSet current = new StateSet();
		current.add(fa.getStartState());
		current = FiniteAutomatonUtil.closure(fa, current);
		
		// simulate the NFA
		for (int i = 0; i < s.length(); i++) {
			char c = s.charAt(i);
			current = FiniteAutomatonUtil.closure(fa, FiniteAutomatonUtil.followAll(fa, current, c));
			if (current.isEmpty()) {
				return Answer.REJECT;
			}
		}

		// if we ended up in a set of States that has at least
		// one accepting state, then the string is accepted
		return FiniteAutomatonUtil.containsAcceptingState(current) ? Answer.ACCEPT : Answer.REJECT;
	}
}
