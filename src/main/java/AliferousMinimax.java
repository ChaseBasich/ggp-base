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
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;


public class AliferousMinimax extends StateMachineGamer {

	private static final long MIN_TIME = 5000;
	private static final long SEARCH_TIME = 500;
	private static final long BUF_TIME = 1500;

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
		long startTime = System.currentTimeMillis();
		while (timeout - System.currentTimeMillis() > BUF_TIME) {
			findTerminalStates(getCurrentState(), startTime, timeout - System.currentTimeMillis() - BUF_TIME);
		}
	}

	private Boolean outOfTime(long timeout) {
		return timeout - System.currentTimeMillis() <= BUF_TIME;
	}

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
		float mobilityFocusScore = numRolesRecip * mobilityHeuristic(state) + (1.0f - numRolesRecip) * focusHeuristic(state);

		//if(goalProximityHeuristic(state) == 0)
		//	score = 2/3 * score + 1/3 * newStateHeuristic(state);
		//else
		float stateScore = newStateHeuristic(state);
		float goalScore = goalProximityHeuristic(state);
		float score = .33f * mobilityFocusScore + .33f * goalScore + .33f * machine.getGoal(state, getRole());


		if ((int)score >= 100) {
			System.out.println("TotalScore: " + Float.toString(score));
			System.out.println("mobilityScore: " + Float.toString(mobilityFocusScore));
			System.out.println("goalScore: " + Float.toString(goalScore));
			System.out.println("Temp score: " + Float.toString(machine.getGoal(state, getRole())));
		}

		return (int) score;
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
			int score = heuristicEval(state);
			return score;
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
			int score = heuristicEval(state);
			return score;
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
			maxScore = 0;
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

		long startTime = System.currentTimeMillis();
		while (System.currentTimeMillis() - startTime < SEARCH_TIME) {
			findTerminalStates(getCurrentState(), startTime, SEARCH_TIME);
		}
		int totalStates = terminalStates.size();
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
