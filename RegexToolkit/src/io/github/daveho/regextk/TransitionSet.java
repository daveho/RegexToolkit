package io.github.daveho.regextk;

import java.util.Collections;
import java.util.SortedSet;
import java.util.TreeSet;

/**
 * A TransitionSet is a set of transitions to the same
 * target state. This is useful for {@link CreateLexicalAnalyzerNFA}
 * in order to emit efficient/compact code to determine whether a
 * transition can be taken based on the most recent scanned
 * character.
 */
public class TransitionSet implements Comparable<TransitionSet> {
	private SortedSet<Character> charSet;
	private int targetStateNumber;
	
	/**
	 * Constructor.
	 * 
	 * @param targetStateNumber the state number of the target state
	 *                          for the transitions in the transition set
	 */
	public TransitionSet(int targetStateNumber) {
		this.charSet = new TreeSet<Character>();
		this.targetStateNumber = targetStateNumber;
	}
	
	/**
	 * Add a character to the transition set, indicating that there
	 * is a transition on this character to the transition set's
	 * target state.
	 * 
	 * @param ch a character
	 */
	public void addChar(char ch) {
		int c = (int)ch;
		if (c < 0 || c > 127)
			throw new IllegalArgumentException("Transition on non-ASCII character " + c);
		charSet.add(ch);
	}
	
	/**
	 * Get the character set.
	 * 
	 * @return the character set
	 */
	public SortedSet<Character> getCharSet() {
		return Collections.unmodifiableSortedSet(charSet);
	}

	/**
	 * Get the target state number.
	 * 
	 * @return the target state number
	 */
	public int getTargetStateNumber() {
		return targetStateNumber;
	}

	/**
	 * Return the number of transitions in this
	 * transition set.
	 * 
	 * @return number of transitions
	 */
	public int size() {
		return charSet.size();
	}

	@Override
	public int compareTo(TransitionSet o) {
		// Sort descending by number of characters
		int sizeDiff = charSet.size() - o.charSet.size();
		if (sizeDiff != 0)
			return -sizeDiff;
		
		// Use target state number as tie-breaker
		return targetStateNumber - o.targetStateNumber;
	}

	/**
	 * Return true IFF this TransitionSet's characters are exactly
	 * the ones in the given string. It is assumed that the string
	 * does not contain duplicate characters.
	 * 
	 * @param chars String containing characters to check
	 * @return true if the TransitionSet has exactly the characters
	 *              in the string
	 */
	public boolean hasExactly(String chars) {
		if (chars.length() != charSet.size())
			return false;
		for (int i = 0; i < chars.length(); ++i)
			if (!charSet.contains(Character.valueOf(chars.charAt(i))))
				return false;
		return true;
	}

	/**
	 * Get a string containing all characters on which there are transitions
	 * in this set.
	 * 
	 * @return string containing all characters on which there are transitions
	 */
	public String membersAsString() {
		StringBuilder buf = new StringBuilder();
		for (Character c : charSet) {
			int ch = c.charValue();
			if (ch < 0 || ch > 127)
				throw new IllegalStateException("non-ASCII character " + ch);
			buf.append((char)ch);
		}
		return buf.toString();
	}
}
