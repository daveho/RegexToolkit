// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013,2017 David H. Hovemeyer <david.hovemeyer@gmail.com>
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

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;
import java.util.Scanner;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/**
 * Import a finite automaton from a JFLAP file.
 */
public class ImportJFLAP {
	/**
	 * Feature which is set if the imported automaton has
	 * any transitions with multiple input symbols (an abomination
	 * allowed by JFLAP.)
	 */
	public static int HAS_TRANSITION_WITH_MULTIPLE_SYMBOLS = 1;
	
	/**
	 * Feature which is set if the imported automaton is
	 * nondeterministic.
	 */
	public static int IS_NONDETERMINISTIC = 2;
	
	private InputStream in;
	private int features;
	
	/**
	 * Constructor.
	 * @param in the InputStream to read from (no attempt will be made to close it)
	 */
	public ImportJFLAP(InputStream in) {
		this.in = in;
		this.features = 0;
	}
	
	/**
	 * Read the JFLAP file and return a {@link FiniteAutomaton}.
	 * 
	 * @return the {@link FiniteAutomaton}
	 * @throws ParserConfigurationException
	 * @throws SAXException
	 * @throws IOException
	 */
	public FiniteAutomaton convert() throws ParserConfigurationException, SAXException, IOException {
		FiniteAutomaton result = new FiniteAutomaton();
		
		Map<Integer, State> idToStateMap = new HashMap<>();
		
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		DocumentBuilder db = factory.newDocumentBuilder();
		Document doc = db.parse(this.in);
		
		Element root = doc.getDocumentElement();
		if (!root.getTagName().equals("structure")) {
			throw new IOException("File is not a JFLAP file?");
		}
		
		Element type = findSingleChild(root, "type");
		String typeVal = type.getTextContent();
		if (!typeVal.equals("fa")) {
			throw new IOException("File is not a finite automaton file?");
		}
		
		Element automaton = findSingleChild(root, "automaton");
		
		// Add states
		NodeList states = automaton.getElementsByTagName("state");
		for (int i = 0; i < states.getLength(); i++) {
			Element stateElt = (Element) states.item(i);
			int id = Integer.parseInt(getAttribute(stateElt,"id"));
			State state = result.createState();
			idToStateMap.put(id, state);
			state.setStart(hasChild(stateElt, "initial"));
			state.setAccepting(hasChild(stateElt, "final"));;
		}
		
		// Add transitions
		NodeList transitions = automaton.getElementsByTagName("transition");
		for (int i = 0; i < transitions.getLength(); i++) {
			Element transElt = (Element) transitions.item(i);
			int from = Integer.parseInt(findSingleChild(transElt, "from").getTextContent());
			int to = Integer.parseInt(findSingleChild(transElt, "to").getTextContent());
			
			if (!idToStateMap.containsKey(from)) {
				throw new IOException("Transition from nonexistent state with id=" + from);
			}
			if (!idToStateMap.containsKey(to)) {
				throw new IOException("Transition to nonexistent state with id=" + to);
			}
			State fromState = idToStateMap.get(from);
			State toState = idToStateMap.get(to);
			
			String sym = findSingleChild(transElt, "read").getTextContent();
			if (sym.isEmpty()) {
				// epsilon transition
				result.createTransition(fromState, toState, FiniteAutomaton.EPSILON);
			} else if (sym.length() == 1) {
				// normal transition on an input symbol
				result.createTransition(fromState, toState, sym.charAt(0));
			} else {
				// JFLAP allows transitions on multiple input symbols:
				// add hidden states so that each transition has a
				// single input symbol
				State last = fromState;
				for (int j = 0; j < sym.length() - 1; j++) {
					char c = sym.charAt(j);
					State hidden = result.createState();
					result.createTransition(last, hidden, c);
					last = hidden;
				}
				result.createTransition(last, toState, sym.charAt(sym.length() - 1));
				
				features |= HAS_TRANSITION_WITH_MULTIPLE_SYMBOLS;
			}
		}
		
		if (!FiniteAutomatonUtil.isDeterministic(result)) {
			features |= IS_NONDETERMINISTIC;
		}
		
		return result;
	}
	
	/**
	 * Check whether the imported automaton has a particular feature.
	 * @param feature the feature to check
	 * @return true if the automaton has the feature, false otherwise
	 */
	public boolean hasFeature(int feature) {
		return (features & feature) != 0;
	}

	/**
	 * Determine whether the imported automaton has any features.
	 * @return true if the imported automaton has at least one feature,
	 *         false otherwise
	 */
	public boolean anyFeatures() {
		return features != 0;
	}
	
	private static Element findSingleChild(Element elt, String tagName) throws IOException {
		NodeList children = elt.getElementsByTagName(tagName);
		if (children.getLength() == 0) {
			throw new IOException(tagName + " element not found");
		}
		if (children.getLength() > 1) {
			throw new IOException("There are multiple " + tagName + " elements");
		}
		return (Element) children.item(0);
	}
	
	private static String getAttribute(Element elt, String attrName) {
		return elt.getAttribute(attrName);
	}
	
	private static boolean hasChild(Element elt, String tagName) {
		NodeList children = elt.getElementsByTagName(tagName);
		return children.getLength() > 0;
	}

	// Just for testing
	public static void main(String[] args) throws Exception {
		@SuppressWarnings("resource")
		Scanner keyboard = new Scanner(System.in);
		System.out.print("Filename: ");
		String fileName = keyboard.nextLine();
		ImportJFLAP im = new ImportJFLAP(new FileInputStream(fileName));
		FiniteAutomaton result = im.convert();
		
		PrintAutomaton printer = new PrintAutomaton();
		printer.print(result);
	}
}
