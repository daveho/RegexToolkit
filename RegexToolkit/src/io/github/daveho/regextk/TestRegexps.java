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

import java.util.NoSuchElementException;
import java.util.Scanner;

/**
 * Interactively test strings against a regular expression.
 * 
 * @author David Hovemeyer
 */
public class TestRegexps {
	public static void main(String[] args) {
		Scanner keyboard = new Scanner(System.in);
		
		System.out.print("Enter a regular expression (use 'e' for epsilon): ");
		String regexp = readLine(keyboard);
		
		// Convert regexp to NFA
		ConvertRegexpToNFA re2nfa = new ConvertRegexpToNFA(regexp);
		FiniteAutomaton nfa = re2nfa.convertToNFA();
		
		// Convert NFA to DFA
		ConvertNFAToDFA nfa2dfa = new ConvertNFAToDFA();
		nfa2dfa.add(nfa);
		FiniteAutomaton dfa = nfa2dfa.execute(FiniteAutomatonTransformerMode.DESTRUCTIVE);
		
		// Allow the user to enter example strings, test them against the DFA
		System.out.println("Enter strings (type 'quit' when done)");
		boolean done = false;
		while (!done) {
			String s = readLine(keyboard);
			if (s == null || s.trim().toLowerCase().equals("quit")) {
				done = true;
			} else {
				s = s.trim();
				
				// If the user entered a literal ε, convert it to the empty string
				// and print a warning
				if (s.equals("ε")) {
					System.out.println("You entered ε, treating it as the empty string");
					s = "";
				}
				
				// Execute the DFA!
				ExecuteDFA exec = new ExecuteDFA();
				exec.setAutomaton(dfa);
				Answer ans = exec.execute(s);
				System.out.println(ans);
			}
		}
	}

	public static String readLine(Scanner keyboard) {
		try {
			return keyboard.nextLine();
		} catch (NoSuchElementException e) {
			return null;
		}
	}
}
