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
	
	// Values to substitute:
	//   - state number data type (two times)
	private static final String YYLEX_LOOKUP_NEXT_STATE =
			"%s yylex_lookup_next_state(const %s *table, int min_cc, int size, int c) {\n" + 
			"  int index;\n" + 
			"  index = c - min_cc;\n" + 
			"  if (index < 0 || index >= size)\n" + 
			"    return -1;\n" + 
			"  else\n" + 
			"    return table[index];\n" + 
			"}\n";

	// Values to substitute:
	//   - state number data type
	//   - state number of start state
	private static final String PREAMBLE =
			"static int yylex(LEXER_TYPE lexer, LEXEME_BUF_TYPE lexeme_buf) {\n" +
			"  %s state = %d, next_state;\n" +
			"  int c;\n" + 
			"  for (;;) {\n" + 
			"    c = GET(lexer);\n" + 
			"    if (c == EOF)\n" + 
			"      break;\n" + 
			"    next_state = -1;\n" + 
			"    switch (state) {\n";

	// Values to substitute:
	//   - signed variant of state number data type
	private static final String END_LOOP_BODY =
			"    } // end switch\n" +
			"    if (((%s) next_state) == -1) {\n" +
			"      UNGET(lexer, c);\n" +
			"      break;\n" +
			"    }\n" +
			"    ADD_TO_LEXEME(lexeme_buf, c);\n" +
			"    state = next_state;\n" +
			"  }\n";
	
	private static final String END_FUNCTION =
			"  return yylex_final_state_to_token_type[state];\n" + 
			"}\n";
	
	// Threshold for allowed number of single-character transitions to the
	// same target state that can't be checked by a predicate function before
	// we emit a set membership test as a bespoke character predicate
	// implementation
	private static final int BITSET_THRESHOLD = 4;
	
	// Threshold for emitting a lookup table for single-character
	// transitions
	private static final int SINGLE_CHAR_TRANSITION_THRESHOLD = 4;
	
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
	 * Generated single-character-transition lookup tables
	 */
	private List<SingleCharTransitionLookupTable> singleCharTransitionLookupTables;
	
	/**
	 * Integer type to use to represent state values.
	 * This is the unsigned version, where the maximum value
	 * is used to represent an invalid state.
	 */
	private String stateNumberType;
	
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
		this.singleCharTransitionLookupTables = new ArrayList<SingleCharTransitionLookupTable>();
		
		// Determine integer type to use to represent state numbers
		// in the generated code. We try to use the smallest unsigned
		// integer type that will work.
		int numStates = table.length;
		if (numStates < 255)
			this.stateNumberType = "uint8_t";
		else if (numStates < 65535)
			this.stateNumberType = "uint16_t";
		else
			this.stateNumberType = "uint32_t";
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
		
		// Write the table classifying the recognized token based on the final state.
		codeGenOutPw.write("static const int yylex_final_state_to_token_type[] = {\n");
		writeFinalStateToTokenTypeTableContents(codeGenOutPw);
		codeGenOutPw.write("};\n\n");
		
		// Write the preamble of the yylex() function
		codeGenOutPw.printf(PREAMBLE, stateNumberType, dfa.getStartState().getNumber());

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
				if (singleCharTransitions.size() >= SINGLE_CHAR_TRANSITION_THRESHOLD) {
					SingleCharTransitionLookupTable lookupTable =
							findOrCreateSingleCharTransitionLookupTable(singleCharTransitions);
					// This MUST be the end of the switch case!
					codeGenOutPw.write("      ");
					if (!firstCondition)
						codeGenOutPw.write("else\n        ");
					codeGenOutPw.printf("next_state = yylex_lookup_next_state(%s, %d, %d, c);\n",
							lookupTable.getName(), lookupTable.getMinCC(), lookupTable.size());
				} else {
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
		
		// Write the end of the state machine loop.
		// Note that we get the signed version of the state number data
		// type by stripping off the leading 'u' character from the
		// type. E.g., "uint8_t" becomes "int8_t".
		codeGenOutPw.printf(END_LOOP_BODY, stateNumberType.substring(1));
		
		// Write the end of the function, which will return the recognized token
		// type based on the final state.
		codeGenOutPw.write(END_FUNCTION);
		
		// End of main generated code (written to codeGenOut via CodeGenOutPw.)
		// Now we can output the full generated code, including helper functions
		// and data structures.
		
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
		
		// If necessary, write definitions of yylex_lookup_next_state function
		// and the supporting single-character transition lookup tables
		if (!singleCharTransitionLookupTables.isEmpty()) {
			out.printf(YYLEX_LOOKUP_NEXT_STATE, stateNumberType, stateNumberType);
			out.write("\n");
			
			for (SingleCharTransitionLookupTable lookupTable : singleCharTransitionLookupTables)
				generateSingleCharTransitionLookupTable(out, lookupTable);
			
			out.write("\n");
		}
		
		// Write the generated yylex function
		String generatedCode = codeGenOut.toString();
		out.write(generatedCode);
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
			// Emit a bitset to serve as a bespoke character predicate
			String cclassName = findOrCreateBitSet(ts.membersAsString());
			out.write("yylex_is_member(&" + cclassName + ", c)");
		} else {
			// Just emit a condition to check the scanned character
			// against specific values
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
		
		// See if this bitset already exists in the list
		for (index = 0; index < predBitsets.size(); ++index) {
			if (predBitsets.get(index).equals(bs))
				break;
		}
		
		// If the bitset hasn't been added yet, add it
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
	
//	private void writeTokenClassifierSwitchStatement(PrintWriter writer) {
//		// Analyze accepting states of the DFA, and determine which token type
//		// is recognized for each one
//		List<State> acceptingStates = dfa.getAcceptingStates();
//		
//		// For DFA accepting states, what token type is recognized
//		String[] dfaStateToRecognizedTokenType = new String[table.length];
//		
//		// Determine which token type is recognized in each DFA accepting state
//		for (State dfaAcceptingState : acceptingStates) {
//			String recognizedTokenType = determineTokenTypeForDFAAcceptingState(dfaAcceptingState);
//			dfaStateToRecognizedTokenType[dfaAcceptingState.getNumber()] = recognizedTokenType;
//		}
//		
//		writer.write("  token_type = -1;\n");
//		writer.write("  switch (state) {\n");
//		
//		for (int state = 0; state < table.length; ++state) {
//			String recognizedTokenType = dfaStateToRecognizedTokenType[state];
//			if (recognizedTokenType != null) {
//				writer.printf("  case %d:\n", state);
//				writer.printf("    token_type = %s;\n", recognizedTokenType); 
//				writer.write("    break;\n");
//			}
//		}
//		
//		writer.write("  }\n");
//	}
	
	private void writeFinalStateToTokenTypeTableContents(PrintWriter writer) {
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
		
		for (int state = 0; state < table.length; ++state) {
			String recognizedTokenType = dfaStateToRecognizedTokenType[state];
			if (recognizedTokenType == null)
				writer.write("  -1,\n"); // not an accepting state
			else
				writer.printf("  %s,\n", recognizedTokenType);
		}
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

	private SingleCharTransitionLookupTable findOrCreateSingleCharTransitionLookupTable(List<TransitionSet> singleCharTransitions) {
		SingleCharTransitionLookupTable singleCharTransitionLookupTable =
				new SingleCharTransitionLookupTable(singleCharTransitions);
		int index;
		
		// Check already-existing lookup tables:
		// if we find an identical one, return it
		for (index = 0; index < singleCharTransitionLookupTables.size(); ++index) {
			SingleCharTransitionLookupTable existingTable = singleCharTransitionLookupTables.get(index);
			if (existingTable.equals(singleCharTransitionLookupTable))
				return existingTable;
		}
		
		// No identical lookup table exists yet, so add it to the
		// list of know lookup tables
		singleCharTransitionLookupTables.add(singleCharTransitionLookupTable);
		singleCharTransitionLookupTable.setName("yylex_lookup_" + index);
		return singleCharTransitionLookupTable;
	}

	private void generateSingleCharTransitionLookupTable(PrintWriter out, SingleCharTransitionLookupTable lookupTable) {
		out.printf("static const %s ", stateNumberType);
		out.write(lookupTable.getName());
		out.write("[] = {\n ");
		int[] lookup = lookupTable.getLookup();
		int col = 0;
		for (int i = 0; i < lookup.length; ++i) {
			if ((col % 15) == 14)
				out.write("\n ");
			out.write(" ");
			out.write(String.valueOf(lookup[i]));
			out.write(",");
			++col;
		}
		out.write("\n};\n");
	}
}
