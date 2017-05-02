import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;


public class AliferousMonteCarlo extends StateMachineGamer {

	private static final long MIN_TIME = 3000;
	private static final long SEARCH_TIME = 0;
	private static final long BUF_TIME = 1500;
	private static final int NUM_CHARGES = 4;

	private int maxScoreFound;
	private int totalScores;

	private Boolean doneSearching;
	private Boolean init = false;
	private ArrayList< HashSet<Move> > totalMoves;
	private HashSet<MachineState> totalStates;
	private ArrayList<MachineState> terminalStates;
	private HashSet<MachineState> terminalStatesSeen;
	private MachineState savedState;

	//monte carlo tree information
	private HashMap<MachineState, Node> stateMetaData;

	@Override
	public StateMachine getInitialStateMachine() {
		totalMoves = new ArrayList< HashSet<Move> >();
		totalStates = new HashSet<MachineState>();
		terminalStates = new ArrayList<MachineState>();
		terminalStatesSeen = new HashSet<MachineState>();
		stateMetaData = new HashMap<MachineState, Node>();

		savedState = null;
		maxScoreFound = 0;
		totalScores = 0;
		StateMachine machine = new CachedStateMachine(new ProverStateMachine());
		return machine;
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		StateMachine machine = getStateMachine();
		MachineState state = machine.getInitialState();
		Node initialNode = new Node(state, null);
		stateMetaData.put(state, initialNode);
		while(!searchTime(timeout)) {
			monteCarlo(state, timeout);
		}
	}

	private Boolean searchTime (long timeout) {
		return timeout - System.currentTimeMillis() <= MIN_TIME;
	}

	private Boolean outOfTime(long timeout) {
		return timeout - System.currentTimeMillis() <= BUF_TIME;
	}

	//---------------------------------------------------------------------------------------------
	//Heuristic Eval Methods
	//---------------------------------------------------------------------------------------------

	private void findTerminalStates(MachineState state, long startTime, long searchTime) throws MoveDefinitionException,
																		TransitionDefinitionException, GoalDefinitionException {
		StateMachine machine = getStateMachine();
		MachineState useState = state;
		if (savedState != null) {
			useState = savedState;
		}

		Random random = new Random();

		while (!machine.isTerminal(useState)) {
			if(System.currentTimeMillis() - startTime > searchTime) {
				savedState = useState;
				return;
			}
			List< List<Move> > jointMoves = machine.getLegalJointMoves(useState);
			useState = machine.getNextState(useState, jointMoves.get(random.nextInt(jointMoves.size())));
		}
		int score = machine.getGoal(useState, getRole());
		if (!terminalStatesSeen.contains(useState)) {
			terminalStates.add(useState);
			terminalStatesSeen.add(useState);
			totalScores += score;
		}
		if (score > maxScoreFound) {
			maxScoreFound = score;
		}
		savedState = null;
	}

	private int newStateHeuristic(MachineState state) throws TransitionDefinitionException,
														MoveDefinitionException, GoalDefinitionException{
		StateMachine machine = getStateMachine();

		List< List<Move> > jointMoves = machine.getLegalJointMoves(state);

		int newState = 0;
		int seenState = 0;

		for(List<Move> moves : jointMoves) {
			MachineState nextState = machine.getNextState(state, moves);
			if (!totalStates.contains(nextState)) {
				newState++;
			}
			else {
				seenState++;
			}
		}
		return (int)(99.0 * (float)newState / (float)(seenState + newState));
	}


	private int mobilityHeuristic(MachineState state) throws TransitionDefinitionException,
														MoveDefinitionException, GoalDefinitionException{
		StateMachine machine = getStateMachine();
		Role myRole = getRole();
		List<Move> myMoves = machine.getLegalMoves(state, myRole);
		Map<Role, Integer> roleMap = machine.getRoleIndices();
		totalMoves.get(roleMap.get(myRole)).addAll(myMoves);
		return (int) (((float)myMoves.size() * 99.0f) / (float)totalMoves.get(roleMap.get(myRole)).size());
	}

	private int focusHeuristic(MachineState state) throws TransitionDefinitionException,
													MoveDefinitionException, GoalDefinitionException{
		StateMachine machine = getStateMachine();
		Role myRole = getRole();
		Map<Role, Integer> roleMap = machine.getRoleIndices();
		List<Role> roles = machine.getRoles();
		int totalScore = 99;
		for (int i = 0; i < roles.size(); i++) {
			if (roles.get(i).equals(myRole)) continue;
			List<Move> moves = machine.getLegalMoves(state, roles.get(i));
			int currScore = 99/(roles.size() - 1) * moves.size() / totalMoves.get(i).size();
			totalScore -= currScore;
		}
		return totalScore;//(myMoves.size() * 99) / totalMoves.size();
	}

	private int goalProximityHeuristic(MachineState state) throws TransitionDefinitionException,
	MoveDefinitionException, GoalDefinitionException{
		StateMachine machine = getStateMachine();
		Role myRole = getRole();

		float averageScore = (float)totalScores / (float)terminalStatesSeen.size();

		float score = 0;
		int closeStates = 0;
		Set<GdlSentence> stateProps = state.getContents();
		for(MachineState termState : terminalStatesSeen) {
			Set<GdlSentence> termStateProps = termState.getContents();
			Set<GdlSentence> intersection = new HashSet<GdlSentence>(termStateProps);
			intersection.retainAll(stateProps);
			float similarity = (float)intersection.size()/termStateProps.size();
			float currScore = (float)machine.getGoal(termState, myRole);
			if (Math.abs(currScore - averageScore) < averageScore / 2.0f ||
					similarity < .65f) {
				continue;
			}
			score +=  similarity * (currScore - averageScore);
			closeStates++;
		}
		return (int) (score / (float)closeStates);
	}

	private int heuristicEval(MachineState state) throws TransitionDefinitionException,
													MoveDefinitionException, GoalDefinitionException{
		StateMachine machine = getStateMachine();
		List<Role> roles = machine.getRoles();

		float numRolesRecip = 1.0f / (float) roles.size();
		float mobilityScore = numRolesRecip * mobilityHeuristic(state);
		float focusScore = (1.0f - numRolesRecip) * focusHeuristic(state);

		//if(goalProximityHeuristic(state) == 0)
		//	score = 2/3 * score + 1/3 * newStateHeuristic(state);
		//else
		//float stateScore = newStateHeuristic(state);
		//float goalScore = goalProximityHeuristic(state);
		float score = .2f * mobilityScore + .6f * focusScore + .2f * machine.getGoal(state, getRole());


		if ((int)score >= 100) {
			System.out.println("TotalScore: " + Float.toString(score));
			//System.out.println("mobilityScore: " + Float.toString(mobilityFocusScore));
			//System.out.println("goalScore: " + Float.toString(goalScore));
			System.out.println("Temp score: " + Float.toString(machine.getGoal(state, getRole())));
		}

		return (int) score;
	}







	//---------------------------------------------------------------------------------------------
	//Monte Carlo Search Methods
	//---------------------------------------------------------------------------------------------
	private float depthCharge(MachineState state, long timeout) throws GoalDefinitionException,
																MoveDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		if (machine.isTerminal(state)) {
			return machine.getGoal(state, getRole());
		}
		if (outOfTime(timeout)) {
			return 0;
		}
		List<Move> moves = machine.getRandomJointMove(state);
		MachineState nextState = machine.getNextState(state, moves);
		return depthCharge(nextState, timeout);
	}

	private float selectionScore(Node node, Node parentNode) {
		float score = node.getScore();

		score += Math.sqrt(2*Math.log(parentNode.getNumVisits())/node.getNumVisits());
		return score;
	}

	private Node select(Node node, long timeout) throws MoveDefinitionException,
														GoalDefinitionException, TransitionDefinitionException {
		if (node.getNumVisits() == 0) {
			return node;
		}

		ArrayList<Node> childNodes = node.getChildren();
		for (Node childNode : childNodes) {
			if (childNode.getNumVisits() == 0) {
				return childNode;
			}
		}

		float maxScore = 0;
		Node bestNode = node;

		for (Node childNode : childNodes) {
			float newScore = selectionScore(childNode, node);
			if (newScore > maxScore) {
				maxScore = newScore;
				bestNode = childNode;
			}
		}
		return select(bestNode, timeout);
	}

	private void expand(Node node) throws MoveDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		MachineState state = node.getState();
		List< List<Move> > jointMoves = machine.getLegalJointMoves(state);

		for (List<Move> jointMove : jointMoves) {
			MachineState nextState = machine.getNextState(state, jointMove);

			Node childNode;
			if (stateMetaData.containsKey(nextState)) {
				childNode = stateMetaData.get(nextState);
				childNode.addParent(node);
			}
			else {
				childNode = new Node(nextState, node);
				stateMetaData.put(nextState, childNode);
			}
			node.addChild(childNode);
		}
	}

	private float simulate(Node node, long timeout) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		float total = 0;
		for (int i = 0; i < NUM_CHARGES; i++) {
			total += depthCharge(node.getState(), timeout);
		}
		return total / NUM_CHARGES;
	}

	private void backpropagate(Node node, float score) {
		node.addVisit();
		node.setScore(node.getScore() + score);
		for (Node parent : node.getParents()) {
			backpropagate(parent, score);
		}
	}


	private float monteCarlo(MachineState state, long timeout) throws MoveDefinitionException,
																GoalDefinitionException, TransitionDefinitionException {
		if (outOfTime(timeout)) {
			return 0;
		}

		Node node;

		if (stateMetaData.containsKey(state)) {
			node = stateMetaData.get(state);
		}
		else {
			node = new Node(state, null);
			stateMetaData.put(state, node);
			System.out.println("Root node");
		}

		Node selected = select(node, timeout);
		expand(selected);
		float score = simulate(selected, timeout);
		backpropagate(selected, score);

		return node.getScore();
	}


	//---------------------------------------------------------------------------------------------
	//Minimax Methods
	//---------------------------------------------------------------------------------------------

	private int maxScore(MachineState state, int alpha, int beta, int level, int max_level, long timeout) throws TransitionDefinitionException,
															MoveDefinitionException, GoalDefinitionException{

		StateMachine machine = getStateMachine();
		Role myRole = getRole();
		if(machine.isTerminal(state)) {
			return machine.getGoal(state, myRole);
		}

		if (outOfTime(timeout)) {
			doneSearching = false;
			return alpha;//TODO: discuss doing heuristic
		}
		if (level > max_level || searchTime(timeout)) {
			doneSearching = false;
			alpha = Math.max((int)monteCarlo(state, timeout), alpha);
			if (alpha >= beta) {
				return beta;
			}
			return alpha;
		}

		List<Move> myMoves = machine.getLegalMoves(state, myRole);

		Map<Role, Integer> roleMap = machine.getRoleIndices();

		for(Move move: myMoves) {
			totalMoves.get(roleMap.get(myRole)).add(move);
			alpha = Math.max(minScore(state, move, alpha, beta, level, max_level, timeout), alpha);
			if (alpha >= beta) {
				return beta;
			}
		}
		return alpha;
	}

	private int minScore(MachineState state, Move myMove, int alpha, int beta, int level, int max_level, long timeout) throws TransitionDefinitionException,
															MoveDefinitionException, GoalDefinitionException{

		StateMachine machine = getStateMachine();

		List< List<Move> > jointMoves = machine.getLegalJointMoves(state, getRole(), myMove);

		Map<Role, Integer> indices = machine.getRoleIndices();

		if (outOfTime(timeout)) {
			doneSearching = false;
			return alpha; //discuss doing heuristic
		}
		if (searchTime(timeout)) {
			doneSearching = false;
			//int score = heuristicEval(state);
			beta = Math.min((int)monteCarlo(state, timeout), beta);
			if (beta <= alpha) {
				return beta;
			}
			return alpha;

		}

		Map<Role, Integer> roleMap = machine.getRoleIndices();
		List<Role> roles = machine.getRoles();
		for (int i = 0; i < roles.size(); i++) {
			if (roles.get(i).equals(getRole())) continue;
			List<Move> moves = machine.getLegalMoves(state, roles.get(i));
			for (Move move : moves) {
				totalMoves.get(i).add(move);
			}
		}



		for(List<Move> moves : jointMoves) {
			MachineState nextState = machine.getNextState(state, moves);

			beta = Math.min(maxScore(nextState, alpha, beta, level + 1, max_level, timeout), beta);
			if (beta <= alpha) {
				return alpha;
			}
		}
		return beta;
	}


	//only for 2-player games
	private Move bestScore(long timeout) throws TransitionDefinitionException,
									MoveDefinitionException, GoalDefinitionException{

		MachineState state = getCurrentState();
		StateMachine machine = getStateMachine();
		Role myRole = getRole();

		List<Move> myMoves = machine.getLegalMoves(state, myRole);

		Random random = new Random();

		int maxScore = 0;
		long startTime = System.nanoTime();
		Move bestMove = myMoves.get(random.nextInt(myMoves.size()));
		int max_depth = 1;
		doneSearching = true;

		Map<Role, Integer> roleMap = machine.getRoleIndices();
		//todo: also, if it finds something before time runs out
		maxScore = 0;
		while (timeout - System.currentTimeMillis() > BUF_TIME) {
			for(Move move: myMoves) {
				totalMoves.get(roleMap.get(myRole)).add(move);
				int score = minScore(state, move, 0, 100, 0, max_depth, timeout);
				if (score == 100) {
					return move;
				}
				if (score > maxScore) {
					maxScore = score;
					bestMove = move;
				}
			}
			if (doneSearching) break;
			max_depth++;
			doneSearching = true;
		}

		return bestMove;
	}


	@Override
	public Move stateMachineSelectMove(long  timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {

		if (!init) {
			StateMachine machine = getStateMachine();
			for (int i = 0; i < machine.getRoles().size(); i++) {
				totalMoves.add(new HashSet<Move> ());
			}
			init = true;
		}
		return bestScore(timeout);
	}

	private void cleanData() {
		System.out.println("done");
		totalMoves.clear();
		totalStates.clear();
		terminalStates.clear();
		terminalStatesSeen.clear();
		stateMetaData.clear();

		savedState = null;
		init = false;
		totalScores = 0;
		maxScoreFound = 0;
	}

	@Override
	public void stateMachineStop() {
		cleanData();
	}

	@Override
	public void stateMachineAbort() {
		cleanData();
	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
	}

	@Override
	public String getName() {
		return "Aliferous-MonteCarlo";
	}

}
