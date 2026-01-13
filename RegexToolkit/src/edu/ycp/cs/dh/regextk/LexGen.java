package edu.ycp.cs.dh.regextk;

import java.io.FileReader;
import java.io.Reader;
import java.util.Scanner;

/**
 * C lexical analyzer generator.
 * This is experimental.
 */
public class LexGen {
	public static void main(String[] args) throws Exception {
		if (args.length != 3) {
			System.err.println("Usage: ava -jar regexToolkit.jar lexgen <specfile> <output C sourcefile>");
			System.exit(1);;
		}
		
		String specfile = args[1];
		String outputSourceFile = args[2];
		
		CreateLexicalAnalyzerFA createLexerFA = new CreateLexicalAnalyzerFA();
		
		// Each entry in the specfile is two lines.
		// - The first line (in an entry) is the token type identifier
		// - the second line (in an entry) is the regex matching the token type
		try (Scanner scanner = new Scanner(new FileReader(specfile))) {
			while (scanner.hasNextLine()) {
				String tokenType = scanner.nextLine();
				String regex = scanner.nextLine();
				
				createLexerFA.addTokenType(tokenType, regex);
			}
		}
		
		System.out.println("Everybody is good!");
	}
}
