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
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class AliferousMinimax extends StateMachineGamer {

	@Override
	public StateMachine getInitialStateMachine() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub

	}


	private int maxScore(MachineState state, Role oponentRole) throws TransitionDefinitionException,
															MoveDefinitionException, GoalDefinitionException{
		StateMachine machine = getStateMachine();
		Role myRole = getRole();

		if(machine.isTerminal(state)) {
			return machine.getGoal(state, myRole);
		}

		List<Move> myMoves = machine.getLegalMoves(state, myRole);

		int maxScore = 0;

		for(Move move: myMoves) {
			int score = minScore(state, oponentRole, move);
			if (score == 100) {
				return 100;
			}
			if (score > maxScore) {
				maxScore = score;
			}
		}

		return maxScore;
	}

	private int minScore(MachineState state, Role oponentRole, Move myMove) throws TransitionDefinitionException,
															MoveDefinitionException, GoalDefinitionException{
		StateMachine machine = getStateMachine();
		List<Move> oponentMoves = machine.getLegalMoves(state, oponentRole);

		Map<Role, Integer> indices = machine.getRoleIndices();

		int minScore = 100;

		for(Move move : oponentMoves) {
			List<Move> currMoves= new ArrayList<Move>(2);
			currMoves.add(indices.get(oponentRole), move);
			currMoves.add(indices.get(getRole()), myMove);

			MachineState nextState = machine.getNextState(state, currMoves);

			int score = maxScore(nextState, oponentRole);
			if (score == 0) {
				return score;
			}
			if (score < minScore) {
				minScore = score;
			}
		}
		return minScore;
	}


	//only for 2-player games
	private Move bestScore() throws TransitionDefinitionException,
									MoveDefinitionException, GoalDefinitionException{
		MachineState state = getCurrentState();
		Role myRole = getRole();

		StateMachine machine = getStateMachine();
		List<Role> allRoles = machine.getRoles();

		//other role
		Role oponentRole = allRoles.get(0);
		if(oponentRole == myRole) {
			oponentRole = allRoles.get(1);
		}


		assert(allRoles.size() == 2);


		List<Move> myMoves = machine.getLegalMoves(state, myRole);


		Random random = new Random();

		int maxScore = 0;
		Move bestMove = myMoves.get(random.nextInt(myMoves.size() - 1));

		for(Move move: myMoves) {
			int score = minScore(state, oponentRole, move);
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
		return "Aliferous-Minimax";
	}

}
