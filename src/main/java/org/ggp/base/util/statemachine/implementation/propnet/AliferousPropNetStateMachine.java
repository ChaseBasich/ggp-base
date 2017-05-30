package org.ggp.base.util.statemachine.implementation.propnet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.And;
import org.ggp.base.util.propnet.architecture.components.Not;
import org.ggp.base.util.propnet.architecture.components.Or;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.architecture.components.Transition;
import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;



public class AliferousPropNetStateMachine extends StateMachine {
	/** The underlying proposition network  */
	private PropNet propNet;
	/** The topological ordering of the propositions */
	private List<Proposition> ordering;
	/** The player roles */
	private List<Role> roles;

	//private methods
	//mark the bases of the propnet
	private void markBases(MachineState state, Set<Proposition> bases) {
		Map<GdlSentence, Proposition> map = propNet.getBasePropositions();
		Set<GdlSentence> sentences = state.getContents();
		for (GdlSentence sentence : sentences) {
			Proposition p = map.get(sentence);
			bases.add(p);
		}
	}

	private void markActions(List<Move> moves, Set<Proposition> inputs) {
		Map<GdlSentence, Proposition> map = propNet.getInputPropositions();
		List<GdlSentence> does = toDoes(moves);
		for (GdlSentence sentence : does) {
			inputs.add(map.get(sentence));
		}
	}

	private Boolean propMarkNegation(Component c, Set<Proposition> props){
		return !getPropMark(c.getSingleInput(), props);
	}

	private Boolean propMarkConjunction(Component c, Set<Proposition> props){
		for ( Component component : c.getInputs() )
		{
			if (!getPropMark(component, props))
			{
				return false;
			}
		}
		return true;
	}

	private Boolean propMarkDisjunction(Component c, Set<Proposition> props){
		for ( Component component : c.getInputs() )
		{
			if ( getPropMark(component, props) )
			{
				return true;
			}
		}
		return false;
	}

	private Boolean isViewProp(Proposition p){
		return p.getType() == Proposition.PropType.VIEW;
	}

	//Methods to find the value of the proposition
	private Boolean getPropMark(Component c, Set<Proposition> props) {
		if (c instanceof Proposition) {
			Proposition p = (Proposition) c;
			if (!isViewProp(p)) {
				return props.contains(p);
			}
			return getPropMark(p.getSingleInput(), props);
		}

		if (c instanceof Not){
			return propMarkNegation(c, props);
		}

		if (c instanceof And){
			return propMarkConjunction(c, props);
		}

		if (c instanceof Or){
			return propMarkDisjunction(c, props);
		}

		if (c instanceof Transition){
			return getPropMark(c.getSingleInput(), props);
		}

		return c.getValue();
	}

	/**
	 *
	 * Used to set the types of all the propositions in the propNet
	 * Types are either VIEW, INPUT, BASE, OTHER
	 */
	private void setTypes() {
		Map<GdlSentence, Proposition> baseProps = propNet.getBasePropositions();
		Map<GdlSentence, Proposition> inputProps = propNet.getInputPropositions();
		for (Proposition p : propNet.getPropositions()) {
			if (inputProps.containsValue(p)) {
				p.setType(Proposition.PropType.INPUT);
			}
			else if (baseProps.containsValue(p)) {
				p.setType(Proposition.PropType.BASE);
			}
			else if (propNet.getInitProposition().equals(p)) {
				p.setType(Proposition.PropType.OTHER);
			}
			else {
				p.setType(Proposition.PropType.VIEW);
			}
		}
	}

	/**
	 * Initializes the PropNetStateMachine. You should compute the topological
	 * ordering here. Additionally you may compute the initial state here, at
	 * your discretion.
	 */
	@Override
	public void initialize(List<Gdl> description) {
		try {
			propNet = OptimizingPropNetFactory.create(description);
			roles = propNet.getRoles();
			ordering = getOrdering();
			setTypes();
		} catch (InterruptedException e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * Computes if the state is terminal. Should return the value
	 * of the terminal proposition for the state.
	 */
	@Override
	public boolean isTerminal(MachineState state) {
		Set<Proposition> props = new HashSet<Proposition>();
		markBases(state, props);
		Boolean result = getPropMark(propNet.getTerminalProposition(), props);
		return result;
	}

	/**
	 * Computes the goal for a role in the current state.
	 * Should return the value of the goal proposition that
	 * is true for that role. If there is not exactly one goal
	 * proposition true for that role, then you should throw a
	 * GoalDefinitionException because the goal is ill-defined.
	 */
	@Override
	public int getGoal(MachineState state, Role role)
			throws GoalDefinitionException {
		Set<Proposition> props = new HashSet<Proposition>();
		markBases(state, props);
		Set<Proposition> goals = propNet.getGoalPropositions().get(role);
		int count = 0;
		Proposition prop = null;
		for(Proposition p : goals){
			if(getPropMark(p, props)){
				count++;
				prop = p;
			}
		}
		if(count == 0){
			return 0;
		}
		if(count == 1){
			return getGoalValue(prop);
		}
		else{
			throw new GoalDefinitionException(state, role);
		}
	}

	/**
	 * Returns the initial state. The initial state can be computed
	 * by only setting the truth value of the INIT proposition to true,
	 * and then computing the resulting state.
	 */
	@Override
	public MachineState getInitialState() {
		Set<Proposition> props = new HashSet<Proposition>();
		props.add(propNet.getInitProposition());
		return getStateFromBase(props);
	}

	/**
	 * Computes the legal moves for role in state.
	 */
	@Override
	public List<Move> getLegalMoves(MachineState state, Role role)
			throws MoveDefinitionException {
		Set<Proposition> props = new HashSet<Proposition>();
		markBases(state, props);
		Set<Proposition> legals = propNet.getLegalPropositions().get(role);
		List<Move> moves = new ArrayList<Move>();
		for (Proposition prop : legals) {
			if (getPropMark(prop, props)) {
				moves.add(getMoveFromProposition(prop));
			}
		}
		return moves;
	}

	/**
	 * Computes the next state given state and the list of moves.
	 */
	@Override
	public MachineState getNextState(MachineState state, List<Move> moves)
			throws TransitionDefinitionException {
		Set<Proposition> props = new HashSet<Proposition>();
		markBases(state, props);
		markActions(moves, props);
		Map<Proposition, Boolean> propMap = new HashMap<Proposition, Boolean>();
		for (Proposition p : propNet.getBasePropositions().values()) {
			propMap.put(p, getPropMark(p.getSingleInput().getSingleInput(), props));
		}
		Set<GdlSentence> contents = new HashSet<GdlSentence>();
		for (Proposition p : propNet.getBasePropositions().values()) {
			if(propMap.get(p)) {
				contents.add(p.getName());
			}
		}
		return new MachineState(contents);
	}

	/**
	 * This should compute the topological ordering of propositions.
	 * Each component is either a proposition, logical gate, or transition.
	 * Logical gates and transitions only have propositions as inputs.
	 *
	 * The base propositions and input propositions should always be exempt
	 * from this ordering.
	 *
	 * The base propositions values are set from the MachineState that
	 * operations are performed on and the input propositions are set from
	 * the Moves that operations are performed on as well (if any).
	 *
	 * @return The order in which the truth values of propositions need to be set.
	 */
	public List<Proposition> getOrdering()
	{
		// List to contain the topological ordering.
		List<Proposition> order = new LinkedList<Proposition>();

		// All of the components in the PropNet
		List<Component> components = new ArrayList<Component>(propNet.getComponents());

		// All of the propositions in the PropNet.
		List<Proposition> propositions = new ArrayList<Proposition>(propNet.getPropositions());

		Stack<Component> stack = new Stack<Component>();

		// Mark all the vertices as not visited
		Map<Component, Boolean> visited = new HashMap<Component, Boolean>();
		for (Component c : components){
			visited.put(c, false);
		}

		// Call the recursive helper function to store
		// Topological Sort starting from all vertices
		// one by one
		for (Component c : components){
			if(!visited.get(c)){
				topologicalSortUtil(c, visited, stack);
			}
		}
		// Print contents of stack
		while (!stack.empty()){
			Component c = stack.pop();
			if(propositions.contains(c)){
				Proposition q = (Proposition) c;
				if(isViewProp(q)){
					order.add(q);
				}
			}
		}
		return order;
	}

	void topologicalSortUtil(Component c, Map<Component,Boolean> visited, Stack<Component> stack)
	{
		// Mark the current node as visited.
		visited.put(c, true);

		// Recur for all the vertices adjacent to this
		// vertex

		for (Component output : c.getOutputs())
		{
			if (!visited.get(output))
				topologicalSortUtil(output, visited, stack);
		}

		// Push current vertex to stack which stores result
		stack.push(c);
	}




	/* Already implemented for you */
	@Override
	public List<Role> getRoles() {
		return roles;
	}

	/* Helper methods */

	/**
	 * The Input propositions are indexed by (does ?player ?action).
	 *
	 * This translates a list of Moves (backed by a sentence that is simply ?action)
	 * into GdlSentences that can be used to get Propositions from inputPropositions.
	 * and accordingly set their values etc.  This is a naive implementation when coupled with
	 * setting input values, feel free to change this for a more efficient implementation.
	 *
	 * @param moves
	 * @return
	 */
	private List<GdlSentence> toDoes(List<Move> moves)
	{
		List<GdlSentence> doeses = new ArrayList<GdlSentence>(moves.size());
		Map<Role, Integer> roleIndices = getRoleIndices();

		for (int i = 0; i < roles.size(); i++)
		{
			int index = roleIndices.get(roles.get(i));
			doeses.add(ProverQueryBuilder.toDoes(roles.get(i), moves.get(index)));
		}
		return doeses;
	}

	/**
	 * Takes in a Legal Proposition and returns the appropriate corresponding Move
	 * @param p
	 * @return a PropNetMove
	 */
	public static Move getMoveFromProposition(Proposition p)
	{
		return new Move(p.getName().get(1));
	}

	/**
	 * Helper method for parsing the value of a goal proposition
	 * @param goalProposition
	 * @return the integer value of the goal proposition
	 */
	private int getGoalValue(Proposition goalProposition)
	{
		GdlRelation relation = (GdlRelation) goalProposition.getName();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
	}

	/**
	 * A Naive implementation that computes a PropNetMachineState
	 * from the true BasePropositions.  This is correct but slower than more advanced implementations
	 * You need not use this method!
	 * @return PropNetMachineState
	 */
	public MachineState getStateFromBase(Set<Proposition> props)
	{
		Map<Proposition, Boolean> propMap = new HashMap<Proposition, Boolean>();
		for (Proposition p : propNet.getBasePropositions().values()) {
			propMap.put(p, getPropMark(p.getSingleInput().getSingleInput(), props));
		}
		Set<GdlSentence> contents = new HashSet<GdlSentence>();
		for (Proposition p : propNet.getBasePropositions().values()) {
			if(propMap.get(p)) {
				contents.add(p.getName());
			}
		}
		return new MachineState(contents);
	}
}