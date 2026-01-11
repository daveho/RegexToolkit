package edu.ycp.cs.dh.regextk;

import java.io.FileReader;
import java.io.Reader;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;

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
		
		// NFA for the entire lexical analyzer
		FiniteAutomaton nfa = new FiniteAutomaton();
		
		// Global start state
		State globalStartState = nfa.createState();
		globalStartState.setStart(true);
		
		Set<String> tokenTypes = new HashSet<String>();
		
		// Map of accepting states to token types
		Map<State, String> acceptingStateToTokenType = new HashMap<State, String>();
		
		// Each entry in the specfile is two lines.
		// - The first line (in an entry) is the token type identifier
		// - the second line (in an entry) is the regex matching the token type
		try (Reader r = new FileReader(specfile)) {
			Scanner scanner = new Scanner(r);
			while (scanner.hasNextLine()) {
				String tokType = scanner.nextLine();
				String regex = scanner.nextLine();
				
				if (tokenTypes.contains(tokType))
					throw new IllegalStateException("Duplicate token type " + tokType);
				
				// Convert the regex to an NFA
				ConvertRegexpToNFA regexToNFA = new ConvertRegexpToNFA(regex);
				FiniteAutomaton tokenNFA = regexToNFA.convertToNFA();
				
				// Make sure that the token NFA has a unique accepting state
				MakeUniqueAcceptingState makeUnique = new MakeUniqueAcceptingState();
				makeUnique.add(tokenNFA);
				tokenNFA = makeUnique.execute(FiniteAutomatonTransformerMode.DESTRUCTIVE);
				
				// Get the unique accepting state
				State tokenAcceptingState = tokenNFA.getUniqueAcceptingState();
				
				// Remember the token type for this accepting state
				acceptingStateToTokenType.put(tokenAcceptingState, tokType);
				
				// Add all token NFA states/transitions to the global NFA
				nfa.addAll(tokenNFA);
				
				// Get the token start state
				State tokenStartState = tokenNFA.getStartState();
				
				// Unflag token start state
				tokenStartState.setStart(false);
				
				// Create epsilon transition from global start state to token NFA start state
				nfa.createTransition(globalStartState, tokenStartState, FiniteAutomaton.EPSILON);
			}
		}
		
		System.out.println("Everybody is good!");
	}
}
