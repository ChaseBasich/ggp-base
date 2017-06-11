import java.util.ArrayList;
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
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.propnet.AliferousForwardPropNetStateMachine;


public class AliferousPropNetPlayer extends StateMachineGamer {

	//Constants - Adjust these to change how the AI structures its time

	//Don't schedule any more new activities (monte carlo, etc) in the final MIN_TIME milliseconds
	private static final long MIN_TIME = 3500;

	//Stops whatever it's doing if time gets down to BUF_TIME milliseconds
	private static final long BUF_TIME = 2500;

	//Number of depth charges per state; we can make this dynamic
	private static final int NUM_CHARGES = 8;

	//Used for heuristics
	private int maxScoreFound;
	private int totalScores;

	//Is it a single player game?
	private Boolean singlePlayer;

	//Whether we should use heuristics or MCTS
	private Boolean useHeuristics = false;

	//Keeps track of the node corresponding to the current state
	private Node currNode;
	//Whether or not currNode needs to be found. This should only be false if we just exited metagame
	private Boolean findNode;

	//Did we reach terminal states in our search? TODO: make this work for monte carlo, I don't think it does yet
	private Boolean doneSearching;

	//Has it been initialized yet? Some things have to be initialized during the first turn of the game
	private Boolean init = false;

	//To avoid re-initializing this each time we make it a private variable. TODO: check thread safety
	private Random random;

	//Keeps track of moves and states seen so far, used for heuristics
	private ArrayList< HashSet<Move> > totalMoves;
	private HashSet<MachineState> totalStates;
	private ArrayList<MachineState> terminalStates;
	private HashSet<MachineState> terminalStatesSeen;
	private MachineState savedState;

	/*During getInitialStateMachine() we initialize all the global data*/
	@Override
	public StateMachine getInitialStateMachine() {
		totalMoves = new ArrayList< HashSet<Move> >();
		totalStates = new HashSet<MachineState>();
		terminalStates = new ArrayList<MachineState>();
		terminalStatesSeen = new HashSet<MachineState>();


		random = new Random();
		savedState = null;
		findNode = true;
		maxScoreFound = 0;
		totalScores = 0;
		singlePlayer = false;
		StateMachine machine = new AliferousForwardPropNetStateMachine();
		return machine;
	}

	/*
	 * (non-Javadoc)
	 * @see org.ggp.base.player.gamer.statemachine.StateMachineGamer#stateMachineMetaGame(long)
	 * Called at the beginning of the metagame. We can use this time to try to figure out information
	 * about the game itself. Currently we determine whether or not it's a single player game and
	 * start expanding the monte carlo tree
	 */
	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		AliferousForwardPropNetStateMachine machine = (AliferousForwardPropNetStateMachine) getStateMachine();
		MachineState state = machine.getInitialState();
		currNode = new Node(state, null, null, true);

		if (machine.getRoles().size() == 1) {
			singlePlayer = true;
			System.out.println("Num subgames " + machine.numSubGames(getRole()));
		}

		long startTime = System.currentTimeMillis();
		machine.getNextState(state, machine.getRandomJointMove(state));
		long totalTime = System.currentTimeMillis() - startTime;

		if(totalTime > 100) {
			useHeuristics = true;
		}
		else {
			while(!searchTime(timeout)) {
				monteCarlo(timeout);
			}
			findNode = false;
		}

		//Call montecarlo until we're out of search time
		//Node.printTree(currNode);
	}

	/*
	 * Helper function to determine whether or not we should stop searching
	 */
	private Boolean searchTime (long timeout) {
		return timeout - System.currentTimeMillis() <= MIN_TIME;
	}

	/*
	 * Helper function to determine whether or not we need to return immediately
	 */
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

	private int maxHeuristicScore(MachineState state, int alpha, int beta, int level, int max_level, long timeout) throws TransitionDefinitionException,
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
			return (int)heuristicEval(state);
		}

		List<Move> myMoves = machine.getLegalMoves(state, myRole);

		Map<Role, Integer> roleMap = machine.getRoleIndices();

		for(Move move: myMoves) {
			totalMoves.get(roleMap.get(myRole)).add(move);
			alpha = Math.max(minHeuristicScore(state, move, alpha, beta, level, max_level, timeout), alpha);
			if (alpha >= beta) {
				return beta;
			}
		}
	return alpha;
	}

	private int minHeuristicScore(MachineState state, Move myMove, int alpha, int beta, int level, int max_level, long timeout) throws TransitionDefinitionException,
		MoveDefinitionException, GoalDefinitionException{

		StateMachine machine = getStateMachine();

		List< List<Move> > jointMoves = machine.getLegalJointMoves(state, getRole(), myMove);

		if (outOfTime(timeout)) {
			doneSearching = false;
			return alpha; //discuss doing heuristic
		}
		if (searchTime(timeout)) {
			return (int)heuristicEval(state);
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

			beta = Math.min(maxHeuristicScore(nextState, alpha, beta, level + 1, max_level, timeout), beta);
			if (beta <= alpha) {
				return alpha;
			}
		}
		return beta;
		}

	private Move bestHeuristicScore(long timeout) throws TransitionDefinitionException,
	MoveDefinitionException, GoalDefinitionException{

			MachineState state = getCurrentState();
			StateMachine machine = getStateMachine();
			Role myRole = getRole();

			List<Move> myMoves = machine.getLegalMoves(state, myRole);

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
					int score = minHeuristicScore(state, move, 0, 100, 0, max_depth, timeout);
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


	//---------------------------------------------------------------------------------------------
	//Monte Carlo Search Methods
	//---------------------------------------------------------------------------------------------
	private float depthCharge(MachineState state, long timeout) throws GoalDefinitionException,
																MoveDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		if (machine.isTerminal(state)) {
			int goal = machine.getGoal(state, getRole());
			return goal;
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

		score += Math.sqrt(1000*log2(parentNode.getNumVisits())/node.getNumVisits());
		return score;
	}

	private Node select(Node node, long timeout) throws MoveDefinitionException,
														GoalDefinitionException, TransitionDefinitionException {
		if (node.getNumVisits() == 0 || node.getChildren().size() == 0) {
			return node;
		}

		ArrayList<Node> childNodes = node.getChildren();
		for (Node childNode : childNodes) {
			if (childNode.getNumVisits() == 0) {
				return childNode;
			}
		}

		float maxScore = 0;
		float childMax = 0;
		float childMin = 100;
		Boolean allTerminal = true;
		Node bestNode = childNodes.get(random.nextInt(childNodes.size()));

		for (Node childNode : childNodes) {
			float newScore = selectionScore(childNode, node);
			if (newScore > maxScore && !(childNode.isTerminal() || childNode.canSeeTerminal())) {
				maxScore = newScore;
				bestNode = childNode;
			}
			if (allTerminal) {
				if (childNode.isTerminal() || childNode.canSeeTerminal()) {
					childMax = Math.max(childMax, childNode.getMax());
					childMin = Math.min(childMin, childNode.getMin());
				}
				else {
					allTerminal = false;
				}
			}
		}
		if (allTerminal) {
			node.setMax(childMax);
			node.setMin(childMin);
			return node;
		}
		return select(bestNode, timeout);
	}

	private void expand(Node node) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException {

		StateMachine machine = getStateMachine();
		MachineState state = node.getState();

		if (machine.isTerminal(state)) {
			node.setTerminal();
			float score = machine.getGoal(state, getRole());
			node.setMax(score);
			node.setMin(score);
			return;
		}
		if (node.getNumVisits() != 0) {
			return;
		}
		//branch for max node vs min node
		if (node.isMaxNode()) {
			for (Move move : machine.getLegalMoves(node.getState(), getRole())) {
				Node childNode;
				MachineState childState = node.getState();
				if (singlePlayer) {
					List<Move> moves = new ArrayList<Move>();
					moves.add(move);
					childState = machine.getNextState(node.getState(), moves);
				}
				childNode = new Node(childState, node, move, singlePlayer); //if singlePlayer, it stays max nodes
				node.addChild(childNode);
			}
		}
		else {
			List< List<Move> > jointMoves = machine.getLegalJointMoves(state, getRole(), node.getMove());

			HashSet<MachineState> childStates = new HashSet<MachineState>();

			for (List<Move> jointMove : jointMoves) {
				MachineState nextState = machine.getNextState(state, jointMove);
				if (childStates.contains(nextState)){
					continue;
				}

				childStates.add(nextState);

				Node childNode;
				childNode = new Node(nextState, node, node.getMove(), true);
				node.addChild(childNode);
			}
		}
	}

	private float simulate(Node node, long timeout) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		float total = 0;
		final float[] results = new float[NUM_CHARGES];
		final Node currNode = node;
		final long time = timeout;
		ArrayList<Thread> threads = new ArrayList<Thread>();
		for (int i = 0; i < NUM_CHARGES; i++) {
			final int index = i;
			threads.add(new Thread() {
				int x = index;
				@Override
				public void run() {
					try {
						results[x] = depthCharge(currNode.getState(), time);
					} catch (GoalDefinitionException | MoveDefinitionException | TransitionDefinitionException e) {
						e.printStackTrace();
					}
				}

			});
			threads.get(i).start();
		}

		for (int i = 0; i < NUM_CHARGES; i++) {
			try {
				threads.get(i).join();
				total += results[i];
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		return total / NUM_CHARGES;
	}

	private void backpropagate(Node node, float score) {
		node.addScore(score);
		if (node.getParent() != null){
			backpropagate(node.getParent(), score);
		}
	}


	private void monteCarlo(long timeout) throws MoveDefinitionException,
																GoalDefinitionException, TransitionDefinitionException {
		if (outOfTime(timeout)) {
			return;
		}

		Node selected = select(currNode, timeout);
		expand(selected);
		float score = simulate(selected, timeout);
		backpropagate(selected, score);
	}

	private int monteCarloSearch(MachineState state, long timeout) throws GoalDefinitionException,
																	MoveDefinitionException, TransitionDefinitionException {
		int total = 0;
		if (outOfTime(timeout)) {
			return 0;
		}
		for (int i = 0; i < NUM_CHARGES; i++) {
			total += depthCharge(state, timeout);
		}
		return total / NUM_CHARGES;
	}


	//--------------------------------------------------------------------------------------------
	//montecarlo minimax
	//--------------------------------------------------------------------------------------------

	/*
	 * Similar to the non-monte carlo minimax, used to search the tree. In this case it searches the tree of nodes
	 * we are constructing. Because this represents our move we always take the maximum score of all the choices.
	 * If it's a single player game it continues calling this recursively. If it's a multiplayer game it calls minScore
	 * next to see which opponent move would minimize our score.
	 */
	private int monteCarloMaxScore(Node node, int alpha, int beta, int level, int max_level, long timeout) throws TransitionDefinitionException,
						MoveDefinitionException, GoalDefinitionException{

		StateMachine machine = getStateMachine();
		Role myRole = getRole();

		//Because we are searching the node tree, get the state associated with that node
		MachineState state = node.getState();
		if (machine.isTerminal(state)) {
			int result = machine.getGoal(state, myRole);
			return result;
		}
		if (node.canSeeTerminal()) {
			return (int) node.getMax();
		}
		//If we're completely out of time, just return immediately
		if (outOfTime(timeout)) {
			doneSearching = false;
			return alpha;
		}
		//If we are at the end of our current search just return the score associated with this child
		if (level > max_level || searchTime(timeout) || node.getChildren().size() == 0) {
			doneSearching = node.getChildren().size() == 0;
			if (node.getNumVisits() < 4) {
				return (int) monteCarloSearch(state, timeout);
			}
			return (int) node.getScore();
		}

		//Continue searching through all the child nodes
		for(Node childNode: node.getChildren()) {
			if (singlePlayer) {
				alpha = Math.max(monteCarloMaxScore(childNode, alpha, beta, level + 1, max_level, timeout), alpha);
			}
			alpha = Math.max(monteCarloMinScore(childNode, alpha, beta, level, max_level, timeout), alpha);
			if (alpha >= beta) {
				return beta;
			}
		}
		return alpha;
	}


	/*
	 * Similar to max score in that it continues searching the tree. Assumes the opponents always take the move that minimizes our player
	 */
	private int monteCarloMinScore(Node node, int alpha, int beta, int level, int max_level, long timeout) throws TransitionDefinitionException,
			MoveDefinitionException, GoalDefinitionException{
		StateMachine machine = getStateMachine();

		if (node.canSeeTerminal()) {
			return (int) node.getMin();
		}

		if (outOfTime(timeout)) {
			doneSearching = false;
			return beta; //discuss doing heuristic
		}
		if (searchTime(timeout) || node.getChildren().size() == 0) {
			return (int)node.getScore();
		}

		for(Node childNode : node.getChildren()) {
			beta = Math.min(monteCarloMaxScore(childNode, alpha, beta, level + 1, max_level, timeout), beta);
			if (beta <= alpha) {
				return alpha;
			}
		}
		return beta;
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
			return (int)monteCarloSearch(state, timeout);
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
			return (int)monteCarloSearch(state, timeout);
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

	private Move bestScore(long timeout) throws TransitionDefinitionException,
									MoveDefinitionException, GoalDefinitionException{

		MachineState state = getCurrentState();
		StateMachine machine = getStateMachine();
		Role myRole = getRole();

		List<Move> myMoves = machine.getLegalMoves(state, myRole);

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


	/*
	 * Finds the best score to take at any given point by searching the monte carlo tree we have created so far, uses minimax
	 */
	private Move bestMonteCarloScore(long timeout) throws TransitionDefinitionException,
												MoveDefinitionException, GoalDefinitionException{

		//Determines the amount of time available to search, which is half of totalTime - bufTime
		//Chose a random move in case we can't decide
		Node bestNode = currNode.getChildren().get(random.nextInt(currNode.getChildren().size()));
		int max_depth = 1;
		doneSearching = true;

		//todo: also, if it finds something before time runs out
		//While there is time left to search
		int maxScore = 0;
		System.out.println("Searching with " + (timeout - System.currentTimeMillis()) + " milli left");
		while (timeout - System.currentTimeMillis() > BUF_TIME) {
			//Find the maximum of all the children
			for(Node childNode: currNode.getChildren()) {
				int score;
				if (singlePlayer) {
					score = monteCarloMaxScore(childNode, 0, 100, 0, max_depth, timeout);
				}
				else {
					score = monteCarloMinScore(childNode, 0, 100, 0, max_depth, timeout);
				}
				if (score == 100) {
					System.out.println("returning 100");
					return childNode.getMove();
				}
				if (score > maxScore) {
					maxScore = score;
					bestNode = childNode;
				}
			}
			if (doneSearching) break;
			max_depth++;
			doneSearching = true;
		}
		System.out.println("Depth achieved: " + (max_depth - 1));

		System.out.println("Chosen Node Score: " + bestNode.getScore());
		System.out.println("Chosen Node visits: " + bestNode.getNumVisits());
		return bestNode.getMove();
	}

	//Finds the node associated with the current state, used at the start of each turn
	private void getCurrentStateNode(long timeout) throws MoveDefinitionException,
													GoalDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		//if there was no previous state, create one
		if (currNode == null) {
			System.out.println("No curr node");
			currNode = new Node(getCurrentState(), null, null, true);
		}
		else {
			Boolean foundNode = false;
			//If it's single player then each state is the child of the previous state as there are no opponent moves
			if (singlePlayer) {
				for (Node childNode : currNode.getChildren()) {
					if (childNode.getState().equals(getCurrentState())) {
						currNode = childNode;
						foundNode = true;
						break;
					}
				}
				if (!foundNode) {
					System.out.println("currnode, but couldn't find state single player");
					currNode = new Node(getCurrentState(), null, null, true);
				}
			}
			//In multiplayer games each state is the grandchild of the previous state due to opponent nodes in between
			else {
				for (Node childNode : currNode.getChildren()) {
					for (Node grandChildNode : childNode.getChildren()) {
						if (grandChildNode.getState().equals(getCurrentState())) {
							currNode = grandChildNode;
							foundNode = true;
							break;
						}
					}
				}
				if (!foundNode) {
					System.out.println("currnode, but couldn't find state, multi");
					currNode = new Node(getCurrentState(), null, null, true);
				}
			}
		}
		//To stop backpropagation at a reasonable point, set the parent to null
		currNode.setParent(null);
		monteCarlo(timeout);
	}

	@Override
	public Move stateMachineSelectMove(long  timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {

		StateMachine machine = getStateMachine();

		if (!init) {

			for (int i = 0; i < machine.getRoles().size(); i++) {
				totalMoves.add(new HashSet<Move> ());
			}
			init = true;
		}

		//If depth charges take too long, run standard heuristic player
		if(useHeuristics) {
			return bestHeuristicScore(timeout);
		}

		//Update the current location int he tree we're constructing
		if (findNode) {
			getCurrentStateNode(timeout);
		}
		System.out.println("\nCurrentNode:");
		currNode.printNode();
		List<Move> moves = machine.getLegalMoves(getCurrentState(), getRole());

		Move result;

		int totalCharges = 0;

		//start by doing MCTS on our current node
		long startTime = System.currentTimeMillis();
		long searchTime = (timeout - startTime - MIN_TIME) / 2;
		while (System.currentTimeMillis() < startTime + searchTime) {
			monteCarlo(timeout);
			totalCharges += 4;
		}
		long timeTaken = System.currentTimeMillis() - startTime;
		float averageCharges = 0.f;
		if (timeTaken > 1000) {
			averageCharges = totalCharges/(timeTaken/1000);
		}
		System.out.println("\nTime taken in milliseconds: " + timeTaken);
		System.out.println("Average forprop-threaded charges per second: " + averageCharges);
		findNode = true;

		//Only find the best move if there is more than 1 choice
		if (moves.size() != 1) {
			result = bestMonteCarloScore(timeout);
		}
		else {
			result = moves.get(0);
		}

		//For the remaining time, do more MCTS
		startTime = System.currentTimeMillis();
		searchTime = (timeout - startTime - BUF_TIME) / 2;
		long remainingTime = (timeout - System.currentTimeMillis() - BUF_TIME) / 1000;
		System.out.println("\nRemaining time: " + remainingTime);
		while (timeout - System.currentTimeMillis() > BUF_TIME) {
			monteCarlo(timeout);
			totalCharges += NUM_CHARGES;
		}
		findNode = true;
		return result;

	}

	private void cleanData() {
		System.out.println("done");
		totalMoves.clear();
		totalStates.clear();
		terminalStates.clear();
		terminalStatesSeen.clear();

		savedState = null;
		singlePlayer = false;
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
		return "Aliferous-ForProp";
	}


	//Utility functions. TODO: make utility class
	public static int log2(int n){
	    return 31 - Integer.numberOfLeadingZeros(n);
	}

}
