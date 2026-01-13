// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013,2014,2017,2026 David H. Hovemeyer <david.hovemeyer@gmail.com>
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

package edu.ycp.cs.dh.regextk;

import java.util.HashMap;
import java.util.Map;

/**
 * General-purpose main entry point.
 * Dispatches to other main methods based on a command argument.
 * 
 * @author David Hovemeyer
 */
public class Main {
	public interface Runner {
		public void exec(String[] args) throws Exception;
	}
	
	private static Map<String, Runner> runnerMap = new HashMap<String, Main.Runner>();
	static {
		runnerMap.put("help", new Runner() { public void exec(String[] args) { printUsage(); } });
		runnerMap.put("check", new Runner() { public void exec(String[] args) { TestRegexps.main(args);} });
		runnerMap.put("equiv", new Runner() { public void exec(String[] args) { DetermineEquivalenceOfRegexps.main(args);} });
		runnerMap.put("batchequiv", new Runner() { public void exec(String[] args) { DetermineEquivalenceOfRegexpsBatch.main(args);} });
		runnerMap.put("grade", new Runner() { public void exec(String[] args) throws Exception { GradeRegexps.main(args);} });
		runnerMap.put("debug", new Runner() { public void exec(String[] args) throws Exception { DebugMain.main(args);} });
		runnerMap.put("gradefa", new Runner() { public void exec(String[] args) throws Exception { GradeFiniteAutomaton.main(args); } });
		runnerMap.put("lexgen", new Runner() {  public void exec(String[] args) throws Exception { LexGen.main(args); } });
	}
	
	public static void main(String[] args) throws Exception {
		if (args.length == 0) {
			printUsage();
			System.exit(1);
		}
		String command = args[0];
		String[] rest = new String[args.length - 1];
		System.arraycopy(args, 1, rest, 0, args.length - 1);
		Runner runner = runnerMap.get(command);
		if (runner == null) {
			System.out.println("Unknown command: " + command);
			printUsage();
			System.exit(1);
		}
		runner.exec(rest);
	}

	private static void printUsage() {
		System.out.println("java -jar regexToolkit.jar <command>");
		System.out.println("Commands are:");
		System.out.println("  help       - print usage information");
		System.out.println("  check      - enter a regexp and use it to classify strings");
		System.out.println("  equiv      - enter two regexps, determine if they're equivalent ");
		System.out.println("  batchequiv - like equiv, but for multiple regexps");
		System.out.println("  grade      - grade regexps");
		System.out.println("  debug      - run debug main");
		System.out.println("  gradefa    - grade JFLAP finite automaton");
		System.out.println("  lexgen     - generate C lexical analyzer");
	}
}
