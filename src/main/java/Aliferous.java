import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

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

public class Aliferous extends StateMachineGamer {

	//how it starts
	@Override
	public StateMachine getInitialStateMachine() {
		// TODO Auto-generated method stub
		return new CachedStateMachine(new ProverStateMachine());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub

	}

	private int maxScore(Move move) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		Queue<MachineState> states = new LinkedList<MachineState>();
		HashSet<MachineState> seenStates = new HashSet<MachineState>();
		//to find out information about the game
		Role role = getRole();
		StateMachine machine = getStateMachine();

		//all of the moves. Because this is single player, it's only our move
		List<Move> moves = new ArrayList<Move>();
		moves.add(move);


		MachineState nextState = machine.getNextState(getCurrentState(), moves);

		int maxScore = 0;

		if(machine.isTerminal(nextState)) {
			return machine.getGoal(nextState, role);
		}

		states.add(nextState);
		seenStates.add(nextState);

		while(!states.isEmpty()) {
			MachineState currState = states.poll();
			List<Move> possibleMoves = null;
			possibleMoves = machine.getLegalMoves(currState, role);

			//loop through all moves
			for(Move newMove : possibleMoves) {
				List<Move> myMove = new ArrayList<Move>();
				myMove.add(newMove);
				MachineState tempState = machine.getNextState(currState, myMove);

				if(machine.isTerminal(tempState)) {
					int score = machine.getGoal(tempState, role);
					if (score == 100) {
						return 100;
					}
					else if (score > maxScore) {
						maxScore = score;
					}
					continue;
				}

				if(seenStates.contains(tempState)) {
					continue;
				}
				states.add(tempState);
			}
		}

		return maxScore;
	}

	private Move getBestMove(List<Move> moves) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		//TODO: error checking
		Move bestMove = moves.get(0);
		int bestScore = 0;
		for(Move move : moves) {
			int score = maxScore(move);
			if (score == 100) {
				return move;
			}
			else if (score > bestScore) {
				bestScore = score;
				bestMove = move;
			}
		}
		return bestMove;
	}

	//when the player is going to make a move
	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub
		MachineState state = getCurrentState();
		Role role = getRole();
		StateMachine machine = getStateMachine();
		List<Move> moves = machine.getLegalMoves(state, role);

		return getBestMove(moves);
	}


	//cleanup
	@Override
	public void stateMachineStop() {
		// TODO Auto-generated method stub

	}

	@Override
	public void stateMachineAbort() {
		// TODO Auto-generated method stub

	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		return "Aliferous";
	}

}
