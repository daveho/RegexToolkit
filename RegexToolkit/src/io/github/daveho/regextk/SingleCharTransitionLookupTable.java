package io.github.daveho.regextk;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * Class representing a set of single-character transitions
 * to different target states. Used to generate a lookup
 * table to efficiently look up the next state based on the
 * most-recently-scanned character.
 */
public class SingleCharTransitionLookupTable {
	private char minCC, maxCC;
	private int[] lookup;
	private String name;
	
	/**
	 * Constructor.
	 * 
	 * @param singleCharTransitions List of single-character {@link TransitionSet}s
	 */
	public SingleCharTransitionLookupTable(List<TransitionSet> singleCharTransitions) {
		SortedMap<Character, Integer> transitions = new TreeMap<Character, Integer>();
		for (TransitionSet ts : singleCharTransitions) {
			if (ts.size() != 1)
				throw new IllegalStateException("TransitionSet size != 1");
			Character ch = ts.getCharSet().first();
			transitions.put(ch, ts.getTargetStateNumber());
		}
		
		// The characters are sorted in ascending order, so we can easily
		// find the minimum and maximum values
		this.minCC = transitions.firstKey().charValue();
		this.maxCC = transitions.lastKey().charValue();
		
		// Build the lookup table
		this.lookup = new int[size()];
		Arrays.fill(lookup, -1);
		for (Map.Entry<Character, Integer> entry : transitions.entrySet()) {
			int index = (int) (entry.getKey().charValue() - minCC);
			lookup[index] = entry.getValue();
		}
	}
	
	/**
	 * Get the minimum character code for any of the transitions.
	 * This is the character code corresponding to element 0 of the lookup
	 * array.
	 * 
	 * @return the minimum character code
	 */
	public int getMinCC() {
		return (int) minCC;
	}

	/**
	 * Get the size (number of entries) of the lookup table.
	 * 
	 * @return size of the lookup table
	 */
	public int size() {
		return ((int) maxCC - (int) minCC) + 1;
	}
	
	/**
	 * Get the lookup table.
	 * 
	 * @return the lookup table
	 */
	public int[] getLookup() {
		return lookup;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this.getClass() != obj.getClass())
			return false;
		SingleCharTransitionLookupTable other = (SingleCharTransitionLookupTable) obj;
		return this.minCC == other.minCC
				&& this.maxCC == other.maxCC
				&& Arrays.equals(lookup, other.lookup);
	}
	
	public void setName(String name) {
		this.name = name;
	}
	
	public String getName() {
		return name;
	}
}
