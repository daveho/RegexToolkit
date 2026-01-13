package io.github.daveho.regextk;

import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Scanner;

/**
 * C lexical analyzer generator.
 * This is experimental.
 */
public class LexGen {
	private int lineNumber;

	public LexGen() {
		lineNumber = 0;
	}

	public void execute(String[] args) throws Exception {
		if (args.length != 2) {
			System.err.println("Usage: java -jar regexToolkit.jar lexgen <specfile> <output C sourcefile>");
			System.exit(1);;
		}

		String specfile = args[0];
		String outputSourceFile = args[1];

		CreateLexicalAnalyzerFA createLexerFA = new CreateLexicalAnalyzerFA();

		// Each entry in the specfile is two lines.
		// - The first line (in an entry) is the token type identifier
		// - the second line (in an entry) is the regex matching the token type
		//
		// Comment lines starting with "#" are allowed (and ignored).
		// Blank lines are also ignored.

		try (Scanner scanner = new Scanner(new FileReader(specfile))) {
			for (;;) {
				String line;
				line = readNonCommentLine(scanner);
				if (line == null)
					break;
				String tokenType = line;
				int tokenTypeLineNumber = lineNumber;
				line = readNonCommentLine(scanner);
				if (line == null)
					throw new IOException("Token type " + tokenType + " missing regex");
				String regex = line;
				createLexerFA.addTokenType(tokenType, regex, tokenTypeLineNumber);
			}
		}

		// Generate the lexer code
		GenerateLexicalAnalyzer generateLexer = new GenerateLexicalAnalyzer(createLexerFA);
		try (PrintWriter writer = new PrintWriter(new FileWriter(outputSourceFile))) {
			generateLexer.generateLexicalAnalyzer(writer);
		}

		System.out.println("Everybody is good!");
	}

	private String readNonCommentLine(Scanner scanner) {
		for (;;) {
			if (!scanner.hasNextLine())
				return null;
			String line = scanner.nextLine();
			++lineNumber;
			line = line.strip();
			if (!line.isEmpty() && !line.startsWith("#"))
				return line;
		}
	}

	public static void main(String[] args) throws Exception {
		LexGen lexGen = new LexGen();
		lexGen.execute(args);
	}
}
