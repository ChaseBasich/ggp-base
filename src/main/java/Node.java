import java.util.ArrayList;

import org.ggp.base.util.statemachine.MachineState;

public class Node {
	//private variables
	private int numVisits;
	private float score;
	private ArrayList<Node> childNodes;
	private Node parentNode;
	private MachineState state;

	public Node(MachineState newState, Node parent) {
		numVisits = 0;
		score = 0;
		childNodes = new ArrayList<Node>();
		state = newState;
		parentNode = parent;
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

	public Node getParent() {
		return parentNode;
	}

	public void setParent(Node parent) {
		parentNode = parent;
	}

	public MachineState getState() {
		return state;
	}
}
