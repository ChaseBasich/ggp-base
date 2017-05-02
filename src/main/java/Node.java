import java.util.ArrayList;

import org.ggp.base.util.statemachine.MachineState;

public class Node {
	//private variables
	private int numVisits;
	private float score;
	private ArrayList<Node> childNodes;
	private ArrayList<Node> parentNodes;
	private MachineState state;

	public Node(MachineState newState, Node parent) {
		numVisits = 0;
		score = 0;
		childNodes = new ArrayList<Node>();
		state = newState;
		parentNodes = new ArrayList<Node>();
		if (parent != null) {
			parentNodes.add(parent);
		}
	}

	//get/set methods
	public int getNumVisits() {
		return numVisits;
	}

	public float getScore() {
		return score;
	}

	public void addVisit() {
		numVisits++;
	}

	public void setScore(float newScore) {
		score = newScore;
	}

	public ArrayList<Node> getChildren() {
		return childNodes;
	}

	public void addChild(Node child) {
		childNodes.add(child);
	}

	public ArrayList<Node> getParents() {
		return parentNodes;
	}

	public void addParent(Node parent) {
		parentNodes.add(parent);
	}

	public MachineState getState() {
		return state;
	}
}
