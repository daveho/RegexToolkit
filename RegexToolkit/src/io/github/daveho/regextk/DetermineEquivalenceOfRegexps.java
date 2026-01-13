// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013,2017 David H. Hovemeyer <david.hovemeyer@gmail.com>
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

import java.util.Scanner;

public class DetermineEquivalenceOfRegexps {
	public static void main(String[] args) {
		@SuppressWarnings("resource")
		Scanner keyboard = new Scanner(System.in);
		
		System.out.print("Regexp A: ");
		String first = keyboard.nextLine();
		
		System.out.print("Regexp B: ");
		String second = keyboard.nextLine();
		
		compareRegexps(first, second, "A", "B");
	}

	public static void compareRegexps(String first, String second, String labelFirst, String labelSecond) {
		FiniteAutomaton a = FiniteAutomatonUtil.convertToNFA(first);
		FiniteAutomaton b = FiniteAutomatonUtil.convertToNFA(second);
		
		boolean equivalent = true;
		
		FiniteAutomaton aMinusB = FiniteAutomatonUtil.difference(a, b);
		if (FiniteAutomatonUtil.recognizesNonEmptyLanguage(aMinusB)) {
			System.out.println(labelSecond + " does not generate some strings in " + labelFirst);
			Util.printExamples(aMinusB, 4);
			equivalent = false;
		}
		
		FiniteAutomaton bMinusA = FiniteAutomatonUtil.difference(b, a);
		if (FiniteAutomatonUtil.recognizesNonEmptyLanguage(bMinusA)) {
			System.out.println(labelSecond + " generates some strings not in " + labelFirst);
			Util.printExamples(bMinusA, 4);
			equivalent = false;
		}
		
		if (equivalent){
			System.out.println("Equivalent!");
		}
	}
}
