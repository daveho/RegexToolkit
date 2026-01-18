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
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

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
			"int yylex_is_member(const struct yylex_charclass *cc, int c) {\n" + 
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
	
	// Special character codes used as shorthands for digits,
	// alphabetic, hex digit, and whitespace. This allows the generated
	// lexer to make use of isxdigit(), isalpha(), isdigit(),
	// and isspace().
	private static final char DIGIT = '\u00f0';
	private static final char ALPHA = '\u00f1';
	private static final char XDIGIT = '\u00f2';
	private static final char SPACE = '\u00f3';
	
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
		for (int stateNumber = 0; stateNumber < table.length; ++stateNumber) {
			// Organize transitions into TransitionSets
			List<TransitionSet> transitionSets = analyzeTransitionTableRow(table[stateNumber]);
			
			// This List records the TransitionSets that represent only
			// a single transition
			List<TransitionSet> singleCharTransitions = new ArrayList<TransitionSet>();
			
			boolean firstCondition = true;
			
			// Iterate through TransitionSets.
			// For the ones with multiple transitions, emit an
			// appropriate predicate check.
			for (TransitionSet ts : transitionSets) {
				if (ts.size() > 1)
					firstCondition = emitPredicateCheck(out, ts, firstCondition);
				else
					singleCharTransitions.add(ts);
			}

			// Handle all transitions on a single character
			if (!singleCharTransitions.isEmpty()) {
				// TODO
			}
		}
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
				
				char ch = (char) (i - minCC);
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
			out.write("    if(");
		else
			out.write("    else if (");
		
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
		
		return false;
	}
	
//	/**
//	 * Write the code of the generated lexical analyzer to
//	 * given {@link PrintWriter}. Note that the caller has responsibility
//	 * for closing the writer.
//	 * 
//	 * @param writer the writer to write the generated code to
//	 * @throws IOException
//	 */
//	public void generateLexicalAnalyzer(PrintWriter out) throws IOException {
//		// StringWriter used to accumulate the generated code,
//		// *without* the generated string constants for bsearch checks.
//		StringWriter generatedCodeWriter = new StringWriter(); 
//		PrintWriter writer = new PrintWriter(generatedCodeWriter);
//		
//		if (DEBUG) {
//			// Analyze accepting states
//			System.out.println("NFA accepting states:");
//			for (State nfaAcceptingState : nfa.getAcceptingStates()) {
//				String tokenType = createLexerNFA.getTokenTypeForAcceptingState(nfaAcceptingState);
//				System.out.printf(" NFA state %d: recognize %s\n", nfaAcceptingState.getNumber(), tokenType);
//			}
//			System.out.println("DFA accepting states:");
//			for (State dfaAcceptingState : dfa.getAcceptingStates()) {
//				StateSet nfaStateSet = converter.getNFAStateSetForDFAState(dfaAcceptingState);
//				System.out.printf("  DFA state %d: NFA states=%s, recognize %s\n",
//						dfaAcceptingState.getNumber(),
//						nfaStateSet,
//						determineTokenTypeForDFAAcceptingState(dfaAcceptingState));
//			}
//		}
//		
//		// BitSets implementing bespoke character predicates
//		List<BitSet> predBitsets = new ArrayList<BitSet>();
//		
//		writer.printf("// Lexical analyzer has %d states\n", table.length);
//		writer.printf(PREAMBLE, dfa.getStartState().getNumber());
//		
//		for (int state = 0; state < table.length; ++state) {
//			int[] row = table[state];
//			Map<Integer, Integer> charToTarget = analyzeRow(row, minCC);
//			
//			if (charToTarget.isEmpty()) {
//				// If there are no outgoing transitions, the state
//				// should be an accepting state. (The NFA, and the DFA constructed
//				// from the NFA, should not have any states that aren't on a
//				// path towards an accepting state.)
//				State dfaState = dfa.getStates().get(state);
//				if (dfaState.getNumber() != state)
//					throw new IllegalStateException("This shouldn't happen");
//				if (!dfaState.isAccepting())
//					throw new IllegalStateException("No transitions from state " + state +
//							", but it's not an accepting state");
//				continue;
//			}
//
//			// There is at least one outgoing transition in this state
//			writer.printf("    case %d:\n", state);
//
//			// Build an array, indexed by target states, with strings
//			// containing the characters on which there is a transition to
//			// the target state. We use use the character codes
//			String[] transitionChars = new String[table.length];
//			Arrays.fill(transitionChars, "");
//
//			// See if we can leverage isxdigit, isalpha, isdigit, and/or isspace
//			
//			int onHexDigit = checkCharacterPred(charToTarget, ConvertRegexpToNFA.HEX_DIGITS);
//			if (onHexDigit != -1)
//				transitionChars[onHexDigit] += XDIGIT;
//
//			int onDigit = checkCharacterPred(charToTarget, ConvertRegexpToNFA.DIGITS);
//			if (onDigit != -1)
//				transitionChars[onDigit] += DIGIT;
//
//			int onAlpha = checkCharacterPred(charToTarget, ConvertRegexpToNFA.ALPHA);
//			if (onAlpha != -1)
//				transitionChars[onAlpha] += ALPHA;
//
//			int onSpace = checkCharacterPred(charToTarget, ConvertRegexpToNFA.WHITESPACE);
//			if (onSpace != -1)
//				transitionChars[onSpace] += SPACE;
//			
//			// Special case: for states where the DFA hasn't decided definitively between
//			// a keyword and an identifier, it's possible that there are transitions on
//			// all alphabetic characters, but they don't all go to the same target state,
//			// even though MOST transitions on alphabetic characters do go to one specific
//			// target state. In this case, we can still make use of isalpha(), as long as the
//			// "special" alphabetic characters are handled first.
//			int nonExclusiveOnAlphaTargetState = checkNonExclusveCharacterPred(charToTarget, ConvertRegexpToNFA.ALPHA);
//			
//			// Similar case for nonexclusive use of isdigit()
//			int nonExclusiveOnDigitTargetState = checkNonExclusveCharacterPred(charToTarget, ConvertRegexpToNFA.DIGITS);
//			
//			boolean firstCondition = true;
//			for (Map.Entry<Integer, Integer> entry : charToTarget.entrySet()) {
//				transitionChars[entry.getValue()] += (char) entry.getKey().intValue();
//			}
//			
//			for (int targetState = 0; targetState < table.length; ++targetState) {
//				// All of the characters on which we have transitions to this
//				// target state
//				String labels = transitionChars[targetState];
//
//				// See how many transitions we have that aren't handled by
//				// a call to a predicate function. If there are enough,
//				// generate a bitset to serve as a bespoke predicate.
//				int nonPredicateTransitions = countNonPredicateTransitions(labels);
//				String bespokePredSetMembers = "";
//				if (nonPredicateTransitions > BITSET_THRESHOLD) {
//					int predicateTransitions = labels.length() - nonPredicateTransitions;
//					// Predicate transitions are always at the beginning of the labels string
//					bespokePredSetMembers = labels.substring(predicateTransitions);
//					
//					// Remove the characters now being handled by yylex_is_member
//					// from the labels string
//					labels = labels.substring(0, predicateTransitions);
//				}
//
//				if (!labels.isEmpty() || !bespokePredSetMembers.isEmpty()) {
//					writer.write("      ");
//					boolean wasFirstCondition = firstCondition;
//					if (!firstCondition)
//						writer.write("else ");
//					else
//						firstCondition = false;
//					writer.write("if (");
//					
//					boolean emittedSetMembershipTest = false;
//					if (!bespokePredSetMembers.isEmpty()) {
//						String bitsetInstanceName = findOrCreateBitSet(predBitsets, bespokePredSetMembers);
//						
//						writer.write("yylex_is_member(&");
//						writer.write(bitsetInstanceName);
//						writer.write(", c)");
//						
//						emittedSetMembershipTest = true;
//					}
//					
//					for (int j = 0; j < labels.length(); ++j) {
//						if (emittedSetMembershipTest || j > 0)
//							writer.printf(" ||\n          %s", wasFirstCondition ? "" : "     ");
//						int ch = labels.charAt(j);
//						switch (ch) {
//						case DIGIT:
//							writer.write("isdigit(c)");
//							break;
//						case ALPHA:
//							writer.write("isalpha(c)");
//							break;
//						case XDIGIT:
//							writer.write("isxdigit(c)");
//							break;
//						case SPACE:
//							writer.write("isspace(c)");
//							break;
//						default:
//							writer.printf("c == '%s'", charLiteralEscape(ch));
//							break;
//						}
//					}
//					writer.write(")\n");
//					writer.printf("        next_state = %d;\n", targetState);
//				}
//			}
//			if (nonExclusiveOnAlphaTargetState != -1)
//				firstCondition = emitNonExclusivePredicateCheck(writer, nonExclusiveOnAlphaTargetState, firstCondition, "isalpha");
//			if (nonExclusiveOnDigitTargetState != -1)
//				firstCondition = emitNonExclusivePredicateCheck(writer, nonExclusiveOnDigitTargetState, firstCondition, "isdigit");
//			writer.write("      break;\n");
//		}
//		writer.write("    }\n");
//		writer.write(END_LOOP_BODY);
//		
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
//
//		writer.write(END_FUNCTION);
//		
//		writer.flush();
//		String generatedCode = generatedCodeWriter.toString();
//
//		// If necessary, write out the definitions of the
//		// yylex_charclass struct type and yylex_is_member() function,
//		// and the bitset instances for each bespoke predicate
//		if (!predBitsets.isEmpty()) {
//			out.write(YYLEX_IS_MEMBER);
//			out.write("\n");
//			
//			for (int i = 0; i < predBitsets.size(); ++i) {
//				BitSet predBitset = predBitsets.get(i);
//				String bitsetName = "yylex_cclass_" + i;
//				out.write("static const struct yylex_charclass ");
//				out.write(bitsetName);
//				out.write(" = {\n");
//				out.write("  { ");
//				int[] bitsetWords = getBitsetWords(predBitset);
//				for (int j = 0; j < bitsetWords.length; ++j)
//					out.printf("0x%x, ", bitsetWords[j]);
//				out.write("}\n");
//				out.write("};\n");
//			}
//			
//			out.write("\n");
//		}
//		
//		// Write generated code
//		out.write(generatedCode);
//	}

	private String findOrCreateBitSet(String setMembers) {
		// Construct a BitSet representing the character codes of
		// the set members
		BitSet bs = new BitSet();
		for (int i = 0; i < setMembers.length(); ++i) {
			int ch = setMembers.charAt(i);
			if (ch < 0 || ch > 127)
				throw new IllegalStateException("non-ASCII character code");
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
	
//	private int[] getBitsetWords(BitSet predBitset) {
//		if (predBitset.cardinality() == 0)
//			throw new IllegalStateException("dafuq?");
//		long[] a = predBitset.toLongArray();
//		if (a.length == 0)
//			throw new IllegalStateException("wut?");
//		int[] result = new int[4];
//		if (a.length > 0) {
//			result[0] = (int) (a[0] & 0xFFFFFFFFL);
//			result[1] = (int) ((a[0] >> 32) & 0xFFFFFFFFL);
//		}
//		if (a.length > 1) {
//			result[2] = (int) (a[1] & 0xFFFFFFFFL);
//			result[3] = (int) ((a[1] >> 32) & 0xFFFFFFFFL);
//		}
//		return result;
//	}
//
//	private int countNonPredicateTransitions(String labels) {
//		int count = 0;
//		for (int i = 0; i < labels.length(); ++i) {
//			int c = labels.charAt(i);
//			if (c != DIGIT && c != ALPHA && c != XDIGIT && c != SPACE)
//				++count;
//		}
//		return count;
//	}

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

//	/**
//	 * Analyze a row of the transition table by returning a map of
//	 * character codes to target states. Character codes having no
//	 * transition are omitted from the map.
//	 * 
//	 * @param row a transition table rows
//	 * @param minCC the character code of the first column of the row
//	 * @return map of character codes to target states
//	 */
//	private Map<Integer, Integer> analyzeRow(int[] row, int minCC) {
//		Map<Integer, Integer> result = new HashMap<Integer, Integer>();
//		for (int i = 0; i < row.length; ++i) {
//			if (row[i] >= 0) {
//				int ch = i + minCC;
//				if (ch > 127)
//					throw new IllegalStateException("Transition on non-ASCII character code " + ch);
//				result.put(ch, row[i]);
//			}
//		}
//		return result;
//	}
//
//	/**
//	 * Check whether all characters in a character class have transitions
//	 * to the same target state. If so, return the state number of that state,
//	 * and also remove the entries for those characters from the char to target
//	 * map.
//	 * 
//	 * @param charToTarget map of characters to target states
//	 * @param charClass characters in a character class
//	 * @return target state for all characters in class, or -1
//	 *         it isn't the case that all of the characters have transitions
//	 *         to the same target state
//	 */
//	private int checkCharacterPred(Map<Integer, Integer> charToTarget, String charClass) {
//		int targetState = -1;
//		for (int i = 0; i < charClass.length(); ++i) {
//			int ch = (int) charClass.charAt(i);
//			Integer t = charToTarget.get(ch);
//			if (t == null)
//				// No transition on this character
//				return -1;
//			if (targetState == -1)
//				targetState = t;
//			else if (targetState != t)
//				// Not all characters in the character class transition to the
//				// same target state
//				return -1;
//		}
//		
//		// If we got here, then all characters in the character class
//		// transition to the same target state. Remove their entries from
//		// the char to target map
//		for (int i = 0; i < charClass.length(); ++i) {
//			charToTarget.remove((int) charClass.charAt(i));
//		}
//		
//		return targetState;
//	}
//
//	private boolean allCovered(Map<Integer, Integer> charToTarget, String charClass) {
//		for (int i = 0; i < charClass.length(); ++i) {
//			if (!charToTarget.containsKey((int) charClass.charAt(i)))
//				return false;
//		}
//		return true;
//	}
//
//	private int checkNonExclusveCharacterPred(Map<Integer, Integer> charToTarget, String charClass) {
//		int nonExclusiveTargetState = -1;
//		if (allCovered(charToTarget, charClass)) {
//			// For each target state reached by an alphabetic character,
//			// count how many transitions target it.
//			Map<Integer, Integer> hist = new HashMap<Integer, Integer>();
//			for (int i = 0; i < charClass.length(); ++i) {
//				int ch = charClass.charAt(i);
//				int targetState = charToTarget.get(ch);
//				if (!hist.containsKey(targetState))
//					hist.put(targetState, 1);
//				else
//					hist.put(targetState, hist.get(targetState) + 1);
//			}
//
//			// Determine which state was transitioned to the most often (and thus
//			// is a candidate for being selected by the character class predicate
//			// (e.g., isalpha()) after transitions on the other states
//			// have been eliminated)
//			int mostFrequentTargetState = -1;
//			int highestTransitionCount = 0;
//			for (Map.Entry<Integer, Integer> entry : hist.entrySet()) {
//				if (mostFrequentTargetState == -1 || entry.getValue() > highestTransitionCount) {
//					mostFrequentTargetState = entry.getKey();
//					highestTransitionCount = entry.getValue();
//				}
//			}
//			
//			// Make a note of which state will use the character class predicate, and remove
//			// its transitions from charToTarget.
//			nonExclusiveTargetState = mostFrequentTargetState;
//			for (Iterator<Map.Entry<Integer, Integer>> i = charToTarget.entrySet().iterator(); i.hasNext(); ) {
//				Map.Entry<Integer, Integer> entry = i.next();
//				if (entry.getValue() == mostFrequentTargetState)
//					i.remove();
//			}
//		}
//		return nonExclusiveTargetState;
//	}
//
//	private boolean emitNonExclusivePredicateCheck(PrintWriter writer, int targetState, boolean firstCondition, String predName) {
//		writer.write("      ");
//		if (!firstCondition)
//			writer.write("else ");
//		else
//			firstCondition = false;
//		writer.printf("if (%s(c))\n", predName);
//		writer.printf("        next_state = %d;\n", targetState);
//		return firstCondition;
//	}
//
//	private String determineTokenTypeForDFAAcceptingState(State dfaAcceptingState) {
//		// This should only be called with a DFA accepting state
//		if (!dfaAcceptingState.isAccepting())
//			throw new IllegalArgumentException();
//		
//		// Find NFA states corresponding to this DFA state
//		StateSet nfaAcceptingStateSet = converter.getNFAStateSetForDFAState(dfaAcceptingState);
//		
//		// For all of the NFA accepting states in the NFA state set,
//		// determine which token type is recognized
//		Set<String> recognizedTokenTypes = new HashSet<String>();
//		for (State nfaState : nfaAcceptingStateSet.getStates()) {
//			if (nfaState.isAccepting())
//				recognizedTokenTypes.add(createLexerNFA.getTokenTypeForAcceptingState(nfaState));
//		}
//		
//		// At least one of the NFA states should be an accepting state,
//		// meaning that we should find at least one token type
//		if (recognizedTokenTypes.isEmpty())
//			throw new IllegalStateException("No tokens are recognized in DFA state " + dfaAcceptingState.getNumber());
//		
//		// Determine the highest-priority token type recognized in this DFA accepting state
//		String recognizedTokenType = null;
//		for (String tokenType : tokenTypes) {
//			if (recognizedTokenTypes.contains(tokenType)) {
//				recognizedTokenType = tokenType;
//				break;
//			}
//		}
//		if (recognizedTokenType == null) {
//			throw new IllegalStateException();
//		}
//		
//		return recognizedTokenType;
//	}
}
