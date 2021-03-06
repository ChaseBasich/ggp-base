import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Queue;

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
	private int depth;
	private Boolean isTerminal;

	//For use in propagating deterministic information up. Only set if terminal or if all children are terminal
	private float min;
	private float max;
	private boolean seenTerminal;

	public Node(MachineState newState, Node parent, Move newMove, Boolean max) {
		numVisits = 0;
		score = 0;
		childNodes = new ArrayList<Node>();
		state = newState;
		parentNode = parent;
		move = newMove;
		maxNode = max; //if newMove is null, then this is a max node

		if (parent != null) {
			depth = parent.getDepth() + 1;
		}

		isTerminal = false;
	}

	//get/set methods
	public int getNumVisits() {
		return numVisits;
	}

	public void addScore(float newScore) {
		score = Math.min(100, (score * numVisits + newScore) / (numVisits + 1));
		numVisits++;
	}

	public float getScore() {
		if (isTerminal || seenTerminal) {
			if (maxNode) {
				return (int) max;
			}
			else {
				return (int) min;
			}
		}
		return Math.max(Math.min(score, 99), 1);
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

	public int getDepth() {
		return depth;
	}

	public void setDepth(int newDepth) {
		depth = newDepth;
	}

	public void setTerminal() {
		isTerminal = true;
	}

	public Boolean isTerminal() {
		return isTerminal;
	}

	public void setMin(float newMin) {
		min = newMin;
		seenTerminal = true;
	}

	public float getMin() {
		return min;
	}

	public void setMax(float newMax) {
		max = newMax;
		seenTerminal = true;
	}

	public float getMax() {
		return max;
	}

	public Boolean canSeeTerminal() {
		return seenTerminal;
	}

	public void printNode() {
		System.out.println("Node: " + state.toString());
		System.out.println("Move: " + move);
		System.out.println("Score: " + getScore());
		System.out.println("Depth: " + depth);
		System.out.println("Visits: " + numVisits);
		System.out.println("Children: " + childNodes.size());
		System.out.println("Max?: " + maxNode);
		System.out.println("See? " + seenTerminal);
	}

	public static void printTree(Node node) {
		Queue<Node> toPrint = new LinkedList<Node>();
		int depth = -1;
		toPrint.add(node);
		while(!toPrint.isEmpty()) {
			Node curr = toPrint.poll();
			if (curr.getDepth() != depth) {
				depth = curr.getDepth();
				System.out.println("\n\ndepth: " + depth);
			}

			curr.printNode();
			System.out.println("");

			for (Node child : curr.getChildren()) {
				toPrint.add(child);
			}
		}
	}
}
