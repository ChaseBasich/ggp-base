import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;


public class AliferousMinimax extends StateMachineGamer {

	private static final long MIN_TIME = 5000;
	private static final long SEARCH_TIME = 2000;
	private static final long BUF_TIME = 1000;

	private int maxScoreFound;
	private int totalScores;

	private Boolean doneSearching;
	private Boolean init = false;
	private ArrayList< HashSet<Move> > totalMoves;
	private HashSet<MachineState> totalStates;
	private ArrayList<MachineState> terminalStates;
	private HashSet<MachineState> terminalStatesSeen;
	private MachineState savedState;

	@Override
	public StateMachine getInitialStateMachine() {
		totalMoves = new ArrayList< HashSet<Move> >();
		totalStates = new HashSet<MachineState>();
		terminalStates = new ArrayList<MachineState>();
		terminalStatesSeen = new HashSet<MachineState>();
		savedState = null;
		maxScoreFound = 0;
		totalScores = 0;
		StateMachine machine = new CachedStateMachine(new ProverStateMachine());
		return machine;
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
	}

	private Boolean outOfTime(long timeout) {
		return timeout - System.currentTimeMillis() <= BUF_TIME;
	}

	private void findTerminalStates(MachineState state, long startTime) throws MoveDefinitionException,
																		TransitionDefinitionException, GoalDefinitionException {
		StateMachine machine = getStateMachine();
		MachineState useState = state;
		if (savedState != null) {
			useState = savedState;
		}

		Random random = new Random();

		while (!machine.isTerminal(useState)) {
			if(System.currentTimeMillis() - startTime > SEARCH_TIME) {
				savedState = useState;
				return;
			}
			List< List<Move> > jointMoves = machine.getLegalJointMoves(useState);
			useState = machine.getNextState(useState, jointMoves.get(random.nextInt(jointMoves.size())));
		}
		if (!terminalStatesSeen.contains(useState)) {
			terminalStates.add(useState);
			terminalStatesSeen.add(useState);
		}
		int score = machine.getGoal(useState, getRole());
		totalScores += score;
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
		return (int)(99.0 * (float)newState / (seenState + newState));
	}


	private int mobilityHeuristic(MachineState state) throws TransitionDefinitionException,
														MoveDefinitionException, GoalDefinitionException{
		StateMachine machine = getStateMachine();
		Role myRole = getRole();
		List<Move> myMoves = machine.getLegalMoves(state, myRole);
		Map<Role, Integer> roleMap = machine.getRoleIndices();
		return (myMoves.size() * 99) / totalMoves.get(roleMap.get(myRole)).size();
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

	private int heuristicEval(MachineState state) throws TransitionDefinitionException,
													MoveDefinitionException, GoalDefinitionException{
		StateMachine machine = getStateMachine();
		List<Role> roles = machine.getRoles();
		int score = mobilityHeuristic(state) / roles.size();
		float weight = (float)(roles.size() - 1) / (float)roles.size();
		score += focusHeuristic(state) * weight;

		score *= .66;
		score += .33 * newStateHeuristic(state);
		return score;
	}

	private int maxScore(MachineState state, int alpha, int beta, int level, int max_level, long timeout) throws TransitionDefinitionException,
															MoveDefinitionException, GoalDefinitionException{

		StateMachine machine = getStateMachine();
		Role myRole = getRole();
		totalStates.add(state);
		if(machine.isTerminal(state)) {
			return machine.getGoal(state, myRole);
		}

		if (level > max_level || outOfTime(timeout)) {
			doneSearching = false;
			return heuristicEval(state);
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
			return heuristicEval(state);
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
			maxScore = 0;
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

		long startTime = System.currentTimeMillis();
		while (System.currentTimeMillis() - startTime < SEARCH_TIME) {
			findTerminalStates(getCurrentState(), startTime);
		}
		System.out.println(terminalStates.size());
		System.out.println("Max Score = " + Integer.toString(maxScoreFound));
		System.out.println("Average Score = " + Integer.toString(totalScores / terminalStates.size()));

		return bestScore(timeout);
	}

	@Override
	public void stateMachineStop() {
		System.out.println("done");
		totalMoves.clear();
		totalStates.clear();
		terminalStates.clear();
		terminalStatesSeen.clear();
		savedState = null;
		init = false;
		totalScores = 0;
		maxScoreFound = 0;
	}

	@Override
	public void stateMachineAbort() {
		totalMoves.clear();
		totalStates.clear();
		init = false;
		terminalStates.clear();
		terminalStatesSeen.clear();
		savedState = null;
		totalScores = 0;
		maxScoreFound = 0;
	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
	}

	@Override
	public String getName() {
		return "Aliferous-Minimax";
	}

}
