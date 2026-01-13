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
 * Check an unknown FiniteAutomaton against a known one to see if
 * they recognize the same language.
 */
public class EquivalenceChecker {
	private FiniteAutomaton unknown;
	private FiniteAutomaton known;
	private FiniteAutomaton overproduced;
	private FiniteAutomaton underproduced;
	private EquivalenceCheckResult result;

	public EquivalenceChecker() {

	}

	public void setUnknown(FiniteAutomaton unknown) {
		this.unknown = unknown;
	}

	public void setKnown(FiniteAutomaton known) {
		this.known = known;
	}

	private EquivalenceCheckResult doCheck() {
		this.overproduced = FiniteAutomatonUtil.difference(unknown, known);
		this.underproduced = FiniteAutomatonUtil.difference(known, unknown);

		boolean over = FiniteAutomatonUtil.recognizesNonEmptyLanguage(overproduced);
		boolean under = FiniteAutomatonUtil.recognizesNonEmptyLanguage(underproduced);

		if (!over && !under) {
			return EquivalenceCheckResult.EQUIVALENT;
		} else if (!over) {
			return EquivalenceCheckResult.UNDER;
		} else if (!under) {
			return EquivalenceCheckResult.OVER;
		} else {
			return EquivalenceCheckResult.OVER_AND_UNDER;
		}
	}

	public FiniteAutomaton getOverproduced() {
		return overproduced;
	}

	public FiniteAutomaton getUnderproduced() {
		return underproduced;
	}

	public void execute() {
		result = doCheck();
	}

	public EquivalenceCheckResult getResult() {
		return result;
	}

	
	
}
