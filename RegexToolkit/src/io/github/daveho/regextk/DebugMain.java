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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Locale;

/**
 * A main entry point that is mostly useful for debugging/testing.
 * 
 * @author David Hovemeyer
 */
public class DebugMain {
	/**
	 * You can set this flag to true in order to see debugging information
	 * about the states and transitions in the initial NFA and the
	 * converted DFA.
	 */
	private static final boolean DEBUG = true;

	public static void main(String[] args) throws IOException {
		BufferedReader keyboard = new BufferedReader(new InputStreamReader(System.in));

		System.out.print("Enter a regexp: ");
		String regexp = keyboard.readLine();
		ConvertRegexpToNFA nfaBuilder = new ConvertRegexpToNFA(regexp);
		FiniteAutomaton a = nfaBuilder.convertToNFA();
		
		if (DEBUG) {
			System.out.println("NFA:");
			PrintAutomaton pa = new PrintAutomaton();
			pa.print(a);
		}
		
		System.out.println("Initial automaton is " +
				(FiniteAutomatonUtil.isDeterministic(a) ? "deterministic" : "nondeterministic"));
		
		System.out.print("Convert the automaton to a DFA (yes/no)? ");
		boolean convert = keyboard.readLine().toLowerCase(Locale.US).equals("yes");
		if (convert) {
			ConvertNFAToDFA dfaBuilder = new ConvertNFAToDFA();
			dfaBuilder.add(a);
			a = dfaBuilder.execute(FiniteAutomatonTransformerMode.NONDESTRUCTIVE);

			if (DEBUG) {
				System.out.println("DFA:");
				PrintAutomaton pa = new PrintAutomaton();
				pa.print(a);
			}

			System.out.println("Converted automaton is " +
					(FiniteAutomatonUtil.isDeterministic(a) ? "deterministic" : "nondeterministic"));
		}

		ExecuteFiniteAutomaton executor = convert ? new ExecuteDFA() : new ExecuteNFA();
		executor.setAutomaton(a);

		System.out.println("Enter strings:");
		for (;;) {
			String line = keyboard.readLine();
			if (line == null) {
				break;
			}
			
			System.out.println(executor.execute(line));
		}
	}
}
