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

package io.github.daveho.regextk;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Generate a C lexical analyzer.
 * This is experimental, and pretty much everyone is much better
 * off using a proper lexical analyzer generator, e.g., flex.
 * The only reason this code is here is because I'm interested in
 * writing a minimal C compiler, and I'm trying to avoid dependencies
 * on heavyweight tools.
 */
public class GenerateLexicalAnalyzer {
	private static final boolean DEBUG = Boolean.getBoolean("lexgen.debug");
	
	private static final String YYLEX_IS_MEMBER =
			"struct yylex_charclass {\n" + 
			"  uint32_t bits[4];\n" + 
			"};\n" + 
			"\n" + 
			"static int yylex_is_member(const struct yylex_charclass *cc, int c) {\n" + 
			"  int bit_offset, word_index;\n" + 
			"  bit_offset = (c & 0x1F);\n" + 
			"  c >>= 5;\n" + 
			"  word_index = (c & 0x03);\n" + 
			"  c >>= 2;\n" + 
			"  if (c != 0)\n" + 
			"    return 0;\n" + 
			"  return (cc->bits[word_index] & (1U << bit_offset)) != 0U;\n" + 
			"}\n";

	private static final String PREAMBLE =
			"static int yylex(LEXER_TYPE lexer, LEXEME_BUF_TYPE lexeme_buf) {\n" + 
			"  int state = %d, next_state, token_type, c;\n" + 
			"  for (;;) {\n" + 
			"    c = GET(lexer);\n" + 
			"    if (c == EOF)\n" + 
			"      break;\n" + 
			"    next_state = -1;\n" + 
			"    switch (state) {\n";
	
	private static final String END_LOOP_BODY =
			"    } // end switch\n" +
			"    if (next_state == -1) {\n" +
			"      UNGET(lexer, c);\n" +
			"      break;\n" +
			"    }\n" +
			"    ADD_TO_LEXEME(lexeme_buf, c);\n" +
			"    state = next_state;\n" +
			"  }\n";
	
	private static final String END_FUNCTION =
			"  return token_type;\n" + 
			"}\n";
	
	// Threshold for allowed number of single-character transitions to the
	// same target state that can't be checked by a predicate function before
	// we emit a set membership test as a bespoke character predicate
	// implementation
	private static final int BITSET_THRESHOLD = 4;
	
	// Threshold for emitting a lookup table for single-character
	// transitions
	private static final int SINGLE_CHAR_TRANSITION_THRESHOLD = Integer.MAX_VALUE;
	
	/**
	 * The {@link CreateLexicalAnalyzerNFA} object which implements the
	 * lexical analyzer NFA and converts it to a DFA.
	 */
	private CreateLexicalAnalyzerNFA createLexerNFA;
	
	/** Generated lexical analyzer NFA. */
	private FiniteAutomaton nfa;
	
	/** Generated lexical analyzer DFA. */
	private FiniteAutomaton dfa;
	
	/**
	 * The {@link ConvertNFAToDFA} object which implements the conversion
	 * from NFA to DFA. It's extremely important, since it records the
	 * mapping from NFA state sets to DFA states.
	 */
	private ConvertNFAToDFA converter;
	
	/**
	 * List of token types, in descending order of priority.
	 */
	private List<String> tokenTypes;
	
	/**
	 * Character code of the first column in the transition table.
	 */
	private int minCC;
	
	/**
	 * Transition table (rows are states, columns correspond to
	 * character codes.)
	 */
	private int[][] table;
	
	/**
	 * Generated bespoke character class bitsets.
	 * We keep track of these to handle the relatively common
	 * case that the same set of characters is used for outgoing
	 * transitions in multiple states.
	 */
	private List<BitSet> predBitsets;
	
	/**
	 * Constructor.
	 * 
	 * @param createLexerFA the {@link CreateLexicalAnalyzerNFA} object
	 *                      which creates the lexer DFA
	 */
	public GenerateLexicalAnalyzer(CreateLexicalAnalyzerNFA createLexerFA) {
		this.createLexerNFA = createLexerFA;
		this.nfa = createLexerFA.getNFA();
		this.tokenTypes = createLexerFA.getTokenTypes();
		
		// Create DFA from NFA
		this.converter = new ConvertNFAToDFA();
		converter.add(this.nfa);
		this.dfa = converter.execute(FiniteAutomatonTransformerMode.NONDESTRUCTIVE);

		// Create transition table
		ExecuteDFA executeDFA = new ExecuteDFA();
		executeDFA.setAutomaton(dfa);
		this.minCC = executeDFA.getMinCC();
		this.table = executeDFA.getTable();
		
		this.predBitsets = new ArrayList<BitSet>();
	}
	
	/**
	 * Write the code of the generated lexical analyzer to
	 * given {@link PrintWriter}. Note that the caller has responsibility
	 * for closing the writer.
	 * 
	 * @param writer the writer to write the generated code to
	 * @throws IOException
	 */
	public void generateLexicalAnalyzer(PrintWriter out) throws IOException {
		
		// Generate main lexical analyzer code and accumulate data structures
		// we'll need to emit
		
		StringWriter codeGenOut = new StringWriter();
		PrintWriter codeGenOutPw = new PrintWriter(codeGenOut);
		
		// Write the preamble of the yylex() function
		codeGenOutPw.printf(PREAMBLE, dfa.getStartState().getNumber());

		// Write the switch cases of the main finite automaton loop
		for (int stateNumber = 0; stateNumber < table.length; ++stateNumber) {
			
			// Organize transitions into TransitionSets
			List<TransitionSet> transitionSets = analyzeTransitionTableRow(table[stateNumber]);
			
			if (transitionSets.isEmpty())
				// No transitions from this state.
				continue;
			
			codeGenOutPw.printf("    case %d:\n", stateNumber);
			
			// This List records the TransitionSets that represent only
			// a single transition
			List<TransitionSet> singleCharTransitions = new ArrayList<TransitionSet>();
			
			boolean firstCondition = true;
			
			// Iterate through TransitionSets.
			// For the ones with multiple transitions, emit an
			// appropriate predicate check.
			for (TransitionSet ts : transitionSets) {
				if (ts.size() > 1)
					firstCondition = emitPredicateCheck(codeGenOutPw, ts, firstCondition);
				else
					singleCharTransitions.add(ts);
			}

			// Handle all transitions on a single character
			if (!singleCharTransitions.isEmpty()) {
				if (singleCharTransitions.size() >= SINGLE_CHAR_TRANSITION_THRESHOLD)
					throw new IllegalStateException("not yet");
				else {
					// Check single-character transitions one at a time
					for (TransitionSet singleCharTs : singleCharTransitions) {
						if (singleCharTs.size() != 1)
							throw new IllegalStateException("WTF");
						char ch = singleCharTs.getCharSet().first().charValue();
						if (firstCondition)
							codeGenOutPw.write("      if (");
						else
							codeGenOutPw.write("      else if (");
						firstCondition = false;
						codeGenOutPw.write("c == '");
						codeGenOutPw.printf("%s", charLiteralEscape(ch));
						codeGenOutPw.write("')\n");
						codeGenOutPw.printf("        next_state = %d;\n", singleCharTs.getTargetStateNumber());
					}
				}
			}
			
			codeGenOutPw.write("      break;\n");
		}
		
		// Write the end of the state machine loop
		codeGenOutPw.write(END_LOOP_BODY);
		
		// Write the switch statement to compute the recognized token type
		writeTokenClassifierSwitchStatement(codeGenOutPw);
		
		// If necessary, write out the definitions of the
		// yylex_charclass struct type and yylex_is_member() function,
		// and the bitset instances for each bespoke predicate
		if (!predBitsets.isEmpty()) {
			out.write(YYLEX_IS_MEMBER);
			out.write("\n");
			
			for (int i = 0; i < predBitsets.size(); ++i)
				generatePredBitset(out, i, predBitsets.get(i));
			
			out.write("\n");
		}
		
		// Write the generated yylex function
		String generatedCode = codeGenOut.toString();
		out.write(generatedCode);
		out.write(END_FUNCTION);
	}

	/**
	 * Return list of {@link TransitionSet}s representing the transitions
	 * in given truth table row, sorted in descending order by number of
	 * target states. (I.e., the TransitionSet of the target state with
	 * the highest number of transitions will be first.)
	 * 
	 * @param row transition table row
	 * @return list of {@link TransitionSet}s in descending order
	 *         by size
	 */
	private List<TransitionSet> analyzeTransitionTableRow(int[] row) {
		Map<Integer, TransitionSet> targetStateToTransitionSet = new HashMap<Integer, TransitionSet>();
		for (int i = 0; i < row.length; ++i) {
			int targetState = row[i];
			if (targetState >= 0) {
				TransitionSet transitionSet = targetStateToTransitionSet.get(targetState);
				if (transitionSet == null) {
					transitionSet = new TransitionSet(targetState);
					targetStateToTransitionSet.put(targetState, transitionSet);
				}
				
				char ch = (char) (minCC + i);
				transitionSet.addChar(ch);
			}
		}

		// Build sorted list of TransitionSets
		List<TransitionSet> result = new ArrayList<TransitionSet>();
		result.addAll(targetStateToTransitionSet.values());
		Collections.sort(result);
		
		return result;
	}

	/**
	 * Emit a predicate check to implement the transitions in the given
	 * {@link TransitionSet}.
	 * 
	 * @param out the {@link PrintWriter} writing the generated lexical analyzer code
	 * @param ts the {@link TransitionSet}
	 * @param firstCondition true if this is the first transition for the
	 *                       current truth table row
	 * @return always returns false (updated value of firstCondition)
	 */
	private boolean emitPredicateCheck(PrintWriter out, TransitionSet ts, boolean firstCondition) {
		if (firstCondition)
			out.write("      if (");
		else
			out.write("      else if (");
		
		// See if we can use isalpha(), isdigit(), isspace(), or isxdigit()
		if (ts.hasExactly(ConvertRegexpToNFA.ALPHA))
			out.write("isalpha(c)");
		else if (ts.hasExactly(ConvertRegexpToNFA.DIGITS))
			out.write("isdigit(c)");
		else if (ts.hasExactly(ConvertRegexpToNFA.WHITESPACE))
			out.write("isspace(c)");
		else if (ts.hasExactly(ConvertRegexpToNFA.HEX_DIGITS))
			out.write("isxdigit(c)");
		else if (ts.size() >= BITSET_THRESHOLD) {
			String cclassName = findOrCreateBitSet(ts.membersAsString());
			out.write("yylex_is_member(&" + cclassName + ", c)");
		} else {
			boolean first = true;
			for (Character ch : ts.getCharSet()) {
				if (first)
					first = false;
				else
					out.write(" || ");
				out.write("c = '");
				out.write(charLiteralEscape(ch.charValue()));
				out.write("'");
			}
		}
		
		out.write(")\n");
		out.printf("        next_state = %d;\n", ts.getTargetStateNumber());
		
		return false;
	}

	private String findOrCreateBitSet(String setMembers) {
		// Construct a BitSet representing the character codes of
		// the set members
		BitSet bs = new BitSet();
		for (int i = 0; i < setMembers.length(); ++i) {
			int ch = setMembers.charAt(i);
			if (ch < 0 || ch > 127)
				throw new IllegalStateException("non-ASCII character code " + ch);
			bs.set(ch);
		}
		
		int index;
		
		// See if this string already exists in the list
		for (index = 0; index < predBitsets.size(); ++index) {
			if (predBitsets.get(index).equals(bs))
				break;
		}
		
		// If string hasn't been added yet, add it
		if (index == predBitsets.size())
			predBitsets.add(bs);
		
		return "yylex_cclass_" + index;
	}
	
	private int[] getBitsetWords(BitSet predBitset) {
		if (predBitset.cardinality() == 0)
			throw new IllegalStateException("dafuq?");
		long[] a = predBitset.toLongArray();
		if (a.length == 0)
			throw new IllegalStateException("wut?");
		int[] result = new int[4];
		if (a.length > 0) {
			result[0] = (int) (a[0] & 0xFFFFFFFFL);
			result[1] = (int) ((a[0] >> 32) & 0xFFFFFFFFL);
		}
		if (a.length > 1) {
			result[2] = (int) (a[1] & 0xFFFFFFFFL);
			result[3] = (int) ((a[1] >> 32) & 0xFFFFFFFFL);
		}
		return result;
	}

	private String charLiteralEscape(int ch) {
		switch (ch) {
		case '\\':
			return "\\\\";
		case '\t':
			return "\\t";
		case '\n':
			return "\\n";
		case '\r':
			return "\\r";
		case '\f':
			return "\\f";
		case '\'':
			return "\\'";
		default:
			return new String(new char[]{(char)ch});
		}
	}
	
	private void writeTokenClassifierSwitchStatement(PrintWriter writer) {
		// Analyze accepting states of the DFA, and determine which token type
		// is recognized for each one
		List<State> acceptingStates = dfa.getAcceptingStates();
		
		// For DFA accepting states, what token type is recognized
		String[] dfaStateToRecognizedTokenType = new String[table.length];
		
		// Determine which token type is recognized in each DFA accepting state
		for (State dfaAcceptingState : acceptingStates) {
			String recognizedTokenType = determineTokenTypeForDFAAcceptingState(dfaAcceptingState);
			dfaStateToRecognizedTokenType[dfaAcceptingState.getNumber()] = recognizedTokenType;
		}
		
		writer.write("  token_type = -1;\n");
		writer.write("  switch (state) {\n");
		
		for (int state = 0; state < table.length; ++state) {
			String recognizedTokenType = dfaStateToRecognizedTokenType[state];
			if (recognizedTokenType != null) {
				writer.printf("  case %d:\n", state);
				writer.printf("    token_type = %s;\n", recognizedTokenType); 
				writer.write("    break;\n");
			}
		}
		
		writer.write("  }\n");
	}

	private String determineTokenTypeForDFAAcceptingState(State dfaAcceptingState) {
		// This should only be called with a DFA accepting state
		if (!dfaAcceptingState.isAccepting())
			throw new IllegalArgumentException();
		
		// Find NFA states corresponding to this DFA state
		StateSet nfaAcceptingStateSet = converter.getNFAStateSetForDFAState(dfaAcceptingState);
		
		// For all of the NFA accepting states in the NFA state set,
		// determine which token type is recognized
		Set<String> recognizedTokenTypes = new HashSet<String>();
		for (State nfaState : nfaAcceptingStateSet.getStates()) {
			if (nfaState.isAccepting())
				recognizedTokenTypes.add(createLexerNFA.getTokenTypeForAcceptingState(nfaState));
		}
		
		// At least one of the NFA states should be an accepting state,
		// meaning that we should find at least one token type
		if (recognizedTokenTypes.isEmpty())
			throw new IllegalStateException("No tokens are recognized in DFA state " + dfaAcceptingState.getNumber());
		
		// Determine the highest-priority token type recognized in this DFA accepting state
		String recognizedTokenType = null;
		for (String tokenType : tokenTypes) {
			if (recognizedTokenTypes.contains(tokenType)) {
				recognizedTokenType = tokenType;
				break;
			}
		}
		if (recognizedTokenType == null) {
			throw new IllegalStateException();
		}
		
		return recognizedTokenType;
	}

	private void generatePredBitset(PrintWriter out, int i, BitSet predBitset) {
		String bitsetName = "yylex_cclass_" + i;
		out.write("static const struct yylex_charclass ");
		out.write(bitsetName);
		out.write(" = {\n");
		out.write("  { ");
		int[] bitsetWords = getBitsetWords(predBitset);
		for (int j = 0; j < bitsetWords.length; ++j)
			out.printf("0x%x, ", bitsetWords[j]);
		out.write("}\n");
		out.write("};\n");
	}
}
