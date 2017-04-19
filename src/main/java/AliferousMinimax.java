import java.util.ArrayList;
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
	private StateMachine machine;
	private Role myRole;

	public AliferousMinimax() {
		machine = getStateMachine();
		myRole = getRole();
	}


	@Override
	public StateMachine getInitialStateMachine() {
		return new CachedStateMachine(new ProverStateMachine());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
	}

	private int maxScore(MachineState state, Role oponentRole, int alpha, int beta) throws TransitionDefinitionException,
															MoveDefinitionException, GoalDefinitionException{

		if(machine.isTerminal(state)) {
			return machine.getGoal(state, myRole);
		}

		List<Move> myMoves = machine.getLegalMoves(state, myRole);

		for(Move move: myMoves) {
			alpha = Math.max(minScore(state, oponentRole, move, alpha, beta), alpha);
			if (alpha >= beta) {
				return beta;
			}
		}

		return alpha;
	}

	private int minScore(MachineState state, Role oponentRole, Move myMove, int alpha, int beta) throws TransitionDefinitionException,
															MoveDefinitionException, GoalDefinitionException{
		List<Move> oponentMoves = machine.getLegalMoves(state, oponentRole);

		Map<Role, Integer> indices = machine.getRoleIndices();

		for(Move move : oponentMoves) {
			ArrayList<Move> currMoves= new ArrayList<Move>(2);
			currMoves.add(move);
			currMoves.add(move);
			currMoves.set(indices.get(oponentRole), move);
			currMoves.set(indices.get(getRole()), myMove);

			MachineState nextState = machine.getNextState(state, currMoves);

			beta = Math.min(maxScore(nextState, oponentRole, alpha, beta), beta);
			if (beta <= alpha) {
				return alpha;
			}
		}
		return beta;
	}


	//only for 2-player games
	private Move bestScore() throws TransitionDefinitionException,
									MoveDefinitionException, GoalDefinitionException{

		MachineState state = getCurrentState();
		List<Role> allRoles = machine.getRoles();

		//other role
		Role oponentRole = allRoles.get(0);
		if(oponentRole.equals(myRole)) {
			oponentRole = allRoles.get(1);
		}


		assert(allRoles.size() == 2);


		List<Move> myMoves = machine.getLegalMoves(state, myRole);


		Random random = new Random();

		int maxScore = 0;
		Move bestMove = myMoves.get(random.nextInt(myMoves.size()));

		for(Move move: myMoves) {
			int score = minScore(state, oponentRole, move, 0, 100);
			if (score == 100) {
				return move;
			}
			if (score > maxScore) {
				maxScore = score;
				bestMove = move;
			}
		}

		return bestMove;
	}


	@Override
	public Move stateMachineSelectMove(long  timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		assert(false);
		return bestScore();
	}

	@Override
	public void stateMachineStop() {
		System.out.println("done");
	}

	@Override
	public void stateMachineAbort() {
	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
	}

	@Override
	public String getName() {
		return "Aliferous-Minimax";
	}

}
