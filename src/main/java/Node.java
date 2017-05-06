import java.util.ArrayList;

import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;

public class Node {
	//private variables
	private int numVisits;
	private float score;
	private ArrayList<Node> childNodes;
	private Node parentNode;
	private MachineState state;
	private Boolean maxNode;
	private Move move;

	public Node(MachineState newState, Node parent, Move newMove, Boolean max) {
		numVisits = 0;
		score = 0;
		childNodes = new ArrayList<Node>();
		state = newState;
		parentNode = parent;
		move = newMove;
		maxNode = max; //if newMove is null, then this is a max node
	}

	//get/set methods
	public int getNumVisits() {
		return numVisits;
	}

	public float getScore() {
		return score / numVisits;
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

	public Boolean isMaxNode() {
		return maxNode;
	}

	public Move getMove() {
		return move;
	}
}
