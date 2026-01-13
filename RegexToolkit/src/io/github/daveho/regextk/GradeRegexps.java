// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013,2014 David H. Hovemeyer <david.hovemeyer@gmail.com>
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

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;

public class GradeRegexps {
	public static void main(String[] args) throws IOException {
		if (args.length < 2) {
			System.err.println("Usage: " + GradeRegexps.class.getName() + " <solution file> <student file> [<prob number>]");
			System.exit(1);
		}
		
		int probNumber = -1;
		if (args.length >= 3) {
			probNumber = Integer.parseInt(args[2]);
		}
		
		String solutionFile = args[0];
		String studentAnswerFile = args[1];
		
		String[] solutions = readLines(solutionFile);
		String[] studentAnswers = readLines(studentAnswerFile);
		
		if (solutions.length != studentAnswers.length) {
			throw new IllegalArgumentException("Number of answers does not match number of solutions");
		}
		
		for (int i = 0; i < solutions.length; i++) {
			if (probNumber >= 0 && i != probNumber) {
				continue;
			}
			System.out.println("Problem " + (i+1) + ":");
			System.out.println();
			DetermineEquivalenceOfRegexps.compareRegexps(solutions[i], studentAnswers[i], "the language", "Your regular expression");
			System.out.println();
		}
	}

	private static String[] readLines(String fileName) throws IOException {
		BufferedReader r = new BufferedReader(new FileReader(fileName));
		ArrayList<String> a = new ArrayList<String>();
		while (true) {
			String line = r.readLine();
			if (line == null) {
				break;
			}
			a.add(line);
		}
		r.close();
		return a.toArray(new String[a.size()]);
	}
}
