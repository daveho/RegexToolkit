package edu.ycp.cs.dh.regextk;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class CreateLexicalAnalyzerFA {
	/**
	 * Token type identifiers, in the order in which they were added.
	 * When a lexeme matches two token types, the one that is earlier in
	 * this list has priority. 
	 */
	private List<String> tokenTypes;
	
	/**
	 * Map of token type identifiers to accepting final states.
	 */
	private Map<String, State> tokenTypeToAcceptingState;
	
	/**
	 * Map of final states to token types.
	 */
	private Map<State, String> acceptingStateToTokenType;
	
	/**
	 * Global lexical analyzer NFA.
	 */
	private FiniteAutomaton nfa;
	
	/**
	 * Start state of global NFA.
	 */
	private State globalStartState;
	
	public CreateLexicalAnalyzerFA() {
		tokenTypes = new ArrayList<String>();
		tokenTypeToAcceptingState = new HashMap<String, State>();
		acceptingStateToTokenType = new HashMap<State, String>();
		nfa = new FiniteAutomaton();
		globalStartState = nfa.createState();
		globalStartState.setStart(true);
	}
	
	/**
	 * Add a token type and the regex which recognizes its lexemes.
	 * 
	 * @param tokenType the token type identifier
	 * @param regex regular expression matching all lexemes for this token
	 */
	public void addTokenType(String tokenType, String regex) {
		if (tokenType.contains(regex))
			throw new IllegalArgumentException("Duplicate token type: " + tokenType);
		tokenTypes.add(tokenType);
		
		// Build the NFA for this token type, and add it to the global NFA
		// Convert the regex to an NFA

		ConvertRegexpToNFA regexToNFA = new ConvertRegexpToNFA(regex);
		FiniteAutomaton tokenNFA = regexToNFA.convertToNFA();
		
		// Make sure that the token NFA has a unique accepting state
		MakeUniqueAcceptingState makeUnique = new MakeUniqueAcceptingState();
		makeUnique.add(tokenNFA);
		tokenNFA = makeUnique.execute(FiniteAutomatonTransformerMode.DESTRUCTIVE);
		
		// Get the unique accepting state
		State tokenAcceptingState = tokenNFA.getUniqueAcceptingState();
		
		// Associate the token type with its accepting state
		tokenTypeToAcceptingState.put(tokenType, tokenAcceptingState);
		acceptingStateToTokenType.put(tokenAcceptingState, tokenType);
		
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
