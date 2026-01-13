// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013,2017,2026 David H. Hovemeyer <david.hovemeyer@gmail.com>
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

import java.util.ArrayList;
import java.util.Collections;
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
	
	/**
	 * Converter to convert the NFA to a DFA.
	 * We need to keep this around since it has the mappings
	 * of NFA state sets to DFA states, which we need in order
	 * to determine which token type is recognized by each DFA
	 * accepting state.
	 */
	private ConvertNFAToDFA converter;
	
	/**
	 * Generated DFA.
	 */
	private FiniteAutomaton dfa;
	
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
	 * @param lineNumber line number of the token type in the specfile
	 */
	public void addTokenType(String tokenType, String regex, int lineNumber) {
		if (tokenType.contains(regex))
			throw new IllegalArgumentException("At line " + lineNumber + " :Duplicate token type: " + tokenType);
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
		
		// Add all token NFA states/transitions to the global NFA
		nfa.addAll(tokenNFA);
		
		// Get the token start state
		State tokenStartState = tokenNFA.getStartState();
		
		// Unflag token start state
		tokenStartState.setStart(false);
		
		// Associate the token type with its accepting state
		//System.out.printf("NFA state %d: token type=%s\n", tokenAcceptingState.getNumber(), tokenType);
		tokenTypeToAcceptingState.put(tokenType, tokenAcceptingState);
		acceptingStateToTokenType.put(tokenAcceptingState, tokenType);
		
		// Create epsilon transition from global start state to token NFA start state
		nfa.createTransition(globalStartState, tokenStartState, FiniteAutomaton.EPSILON);
	}
	
	/**
	 * Create DFA for recognizing tokens.
	 * @return the DFA recognizing the tokens of the input language
	 */
	public FiniteAutomaton createDFA() {
		if (dfa == null) {
			converter = new ConvertNFAToDFA();
			converter.add(nfa);
			dfa = converter.execute(FiniteAutomatonTransformerMode.NONDESTRUCTIVE);
		}
		return dfa;
	}
	
	/**
	 * Get token types in decreasing order of priority.
	 * 
	 * @return token types
	 */
	public List<String> getTokenTypes() {
		return Collections.unmodifiableList(tokenTypes);
	}
	
	/**
	 * Get the {@link ConvertNFAToDFA} object used to convert the lexical
	 * analyzer NFA to a DFA. This is important, since the NFA accepting states
	 * are associated 1:1 with the token types, and by knowing which NFA
	 * accepting states a DFA accepting state is associated with, we know
	 * what kind of token is recognized by that DFA state.
	 *  
	 * @return the {@link ConvertNFAToDFA} object
	 */
	public ConvertNFAToDFA getConverter() {
		return converter;
	}
	
	/**
	 * Get the token type for given NFA accepting {@link State}.
	 * 
	 * @param nfaAcceptingState the NFA accepting state
	 * @return the token type recognized by the NFA accepting state
	 */
	public String getTokenTypeForAcceptingState(State nfaAcceptingState) {
		if (!nfaAcceptingState.isAccepting())
			throw new IllegalArgumentException("NFA state isn't an accepting state");
		if (!acceptingStateToTokenType.containsKey(nfaAcceptingState))
			throw new IllegalStateException("Can't find token type for NFA state " + nfaAcceptingState.getNumber());
		return acceptingStateToTokenType.get(nfaAcceptingState);
	}
}
