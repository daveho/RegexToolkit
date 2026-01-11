package edu.ycp.cs.dh.regextk;

/**
 * C lexical analyzer generator.
 * This is experimental.
 */
public class LexGen {
	public static void main(String[] args) throws Exception {
		if (args.length != 3) {
			System.err.println("Usage: ava -jar regexToolkit.jar lexgen <specfile>");
			System.exit(1);;
		}
		
		System.out.println("Everybody is good!");
	}
}
