// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013,2014,2017 David H. Hovemeyer <david.hovemeyer@gmail.com>
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

import java.io.FileInputStream;

/**
 * Grade a finite automaton by loading it and a solution
 * from JFLAP files and determining whether or not they are
 * equivalent.
 */
public class GradeFiniteAutomaton {
	public static void main(String[] args) throws Exception {
		if (args.length != 2) {
			System.err.println("Usage: " + GradeFiniteAutomaton.class.getName() + " <student automaton> <solution automaton>");
			System.exit(1);
		}
		
		String studentFile = args[0];
		String solutionFile = args[1];
		
		FiniteAutomaton student = null, solution = null;
		
		try (FileInputStream in = new FileInputStream(studentFile)) {
			ImportJFLAP im = new ImportJFLAP(in);
			student = im.convert();
			System.out.printf("Your automaton has %d state(s)\n", student.getNumStates());
			if (im.hasFeature(ImportJFLAP.HAS_TRANSITION_WITH_MULTIPLE_SYMBOLS)) {
				System.out.println("Your automaton has transition(s) consuming multiple symbols");
			}
			System.out.printf("Your automaton is %sdeterministic\n", im.hasFeature(ImportJFLAP.IS_NONDETERMINISTIC) ? "non" : "");
			System.out.println();
		}
		
		try (FileInputStream in = new FileInputStream(solutionFile)) {
			ImportJFLAP im = new ImportJFLAP(in);
			solution = im.convert();
		}
		
		EquivalenceChecker checker = new EquivalenceChecker();
		checker.setUnknown(student);
		checker.setKnown(solution);
		checker.execute();
		EquivalenceCheckResult result = checker.getResult();
		
		if (result == EquivalenceCheckResult.EQUIVALENT) {
			System.out.println("Equivalent!");
		}
		
		if (result.isUnder()) {
			System.out.println("Your automaton rejects some strings in the language:");
			FiniteAutomaton under = checker.getUnderproduced();
			Util.printExamples(under, 4);
		}
		
		if (result.isOver()) {
			System.out.println("Your automaton accepts some strings not in the language:");
			FiniteAutomaton over = checker.getOverproduced();
			Util.printExamples(over, 4);
		}
	}
}
