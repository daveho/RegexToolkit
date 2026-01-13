package edu.ycp.cs.dh.regextk;

import java.io.IOException;
import java.io.PrintWriter;

/**
 * Generate a C lexical analyzer.
 * This is experimental, and pretty much everyone is much better
 * off using a proper lexical analyzer generator, e.g., flex.
 * The only reason this code is here is because I'm interested in
 * writing a minimal C compiler, and I'm trying to avoid dependencies
 * on heavyweight tools.
 */
public class GenerateLexicalAnalyzer {
	private CreateLexicalAnalyzerFA createLexerFA;
	
	/**
	 * Constructor.
	 * 
	 * @param createLexerFA the {@link CreateLexicalAnalyzerFA} object
	 *                      which created the lexer DFA
	 */
	public GenerateLexicalAnalyzer(CreateLexicalAnalyzerFA createLexerFA) {
		this.createLexerFA = createLexerFA;
	}
	
	/**
	 * Write the code of the generated lexical analyzer to
	 * given {@link PrintWriter}. Note that the caller has responsibility
	 * for closing the writer.
	 * 
	 * @param writer the writer to write the generated code to
	 * @throws IOException
	 */
	public void generateLexicalAnalyzer(PrintWriter writer) throws IOException {
		FiniteAutomaton dfa = createLexerFA.createDFA();
		ExecuteDFA executeDFA = new ExecuteDFA();
		executeDFA.setAutomaton(dfa);
		
		int[][] table = executeDFA.getTable();
		
		writer.printf("// Lexical analyzer has %d states\n", table.length);
	}
}
