package org.ggp.base.util.statemachine.implementation.propnet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.Stack;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.And;
import org.ggp.base.util.propnet.architecture.components.Constant;
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



public class AliferousCachedForwardPropNetStateMachine extends StateMachine {
	/** The underlying proposition network  */
	private PropNet propNet;
	/** The topological ordering of the propositions */
	private List<Component> ordering;
	/** The player roles */
	private List<Role> roles;

	private Map<MachineState, Set<Component> > cache;

	private ArrayList< Set<Component> > threadSets;

	//private methods
	//mark the bases of the propnet
	private void markBases(MachineState state, Set<Component> bases) {
		Map<GdlSentence, Proposition> map = propNet.getBasePropositions();
		Set<GdlSentence> sentences = state.getContents();
		for (GdlSentence sentence : sentences) {
			Proposition p = map.get(sentence);
			bases.add(p);
		}
	}

	private void markActions(List<Move> moves, Set<Component> inputs) {
		Map<GdlSentence, Proposition> map = propNet.getInputPropositions();
		List<GdlSentence> does = toDoes(moves);
		for (GdlSentence sentence : does) {
			inputs.add(map.get(sentence));
		}
	}

	private Boolean propMarkNegation(Component c, Set<Component> props){
		return !props.contains(c.getSingleInput());
	}

	private Boolean propMarkConjunction(Component c, Set<Component> props){
		for ( Component component : c.getInputs() )
		{
			if (!props.contains(component))
			{
				return false;
			}
		}
		return true;
	}

	private Boolean propMarkDisjunction(Component c, Set<Component> props){
		for ( Component component : c.getInputs() )
		{
			if (props.contains(component) )
			{
				return true;
			}
		}
		return false;
	}

	private Boolean propValueNegation(Component c, Set<Component> props){
		return !getPropValue(c.getSingleInput(), props);
	}

	private Boolean propValueConjunction(Component c, Set<Component> props){
		for ( Component component : c.getInputs() )
		{
			if (!getPropValue(component, props))
			{
				return false;
			}
		}
		return true;
	}

	private Boolean propValueDisjunction(Component c, Set<Component> props){
		for ( Component component : c.getInputs() )
		{
			if (getPropValue(component, props))
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
	private Boolean getPropValue(Component c, Set<Component> props) {
		if (c instanceof Proposition) {
			Proposition p = (Proposition) c;
			if (!isViewProp(p)) {
				return props.contains(p);
			}
			return getPropValue(p.getSingleInput(), props);
		}

		if (c instanceof Not){
			return propValueNegation(c, props);
		}

		if (c instanceof And){
			return propValueConjunction(c, props);
		}

		if (c instanceof Or){
			return propValueDisjunction(c, props);
		}

		if (c instanceof Transition){
			return getPropValue(c.getSingleInput(), props);
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

	private void forwardProp(Set<Component> props){
		for(Component p : ordering){
			Boolean addProp = false;
			if(p instanceof Proposition){
				addProp = props.contains(p.getSingleInput());
			}
			else {
				if(p instanceof Not){
					addProp = propMarkNegation(p, props);
				}
				else if(p instanceof And){
					addProp = propMarkConjunction(p, props);
				}
				else if(p instanceof Or){
					addProp = propMarkDisjunction(p, props);
				}
				else if(p instanceof Constant){
					addProp = p.getValue();
				}
				else if (p instanceof Transition) {
					addProp = props.contains(p.getSingleInput());
				}
			}
			if (addProp) {
				props.add(p);
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
			setTypes();
			ordering = getOrdering();
			if (verifySort()) {
				System.out.println("good order");
			}
			else {
				System.out.println("bad order");
			}
		} catch (InterruptedException e) {
			throw new RuntimeException(e);
		}
	}

	public void initializeCache(int numThreads) {
		cache = new HashMap<MachineState, Set<Component> >();
		threadSets = new ArrayList<Set<Component> >();
		for (int i = 0; i < numThreads; i++) {
			threadSets.add(new HashSet<Component>());
		}
	}

	private Set<Component> getProps(MachineState state) {
		Set<Component> props;
		if (cache.containsKey(state)) {
			props = cache.get(state);
		}
		else {
			props = new HashSet<Component>();
			markBases(state, props);
		}
		return props;
	}

	/**
	 * Computes if the state is terminal. Should return the value
	 * of the terminal proposition for the state.
	 */
	@Override
	public boolean isTerminal(MachineState state) {
		Set<Component> props = getProps(state);
		return isTerminalProps(props);
	}

	private boolean isTerminalProps(Set<Component> props) {
		Proposition t = propNet.getTerminalProposition();
		return getPropValue(t, props);
	}

	private int getGoalProps(Role role, Set<Component> props) throws GoalDefinitionException {
		Set<Proposition> goals = propNet.getGoalPropositions().get(role);
		int count = 0;
		Proposition prop = null;
		//getPropMark(p, props)
		for(Proposition p : goals){
			if(getPropValue(p, props)){
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
			MachineState state = getStateFromBase(props, false);
			throw new GoalDefinitionException(state, role);
		}
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
		Set<Component> props = getProps(state);
		return getGoalProps(role, props);
	}

	/**
	 * Returns the initial state. The initial state can be computed
	 * by only setting the truth value of the INIT proposition to true,
	 * and then computing the resulting state.
	 */
	@Override
	public MachineState getInitialState() {
		Set<Component> props = new HashSet<Component>();
		props.add(propNet.getInitProposition());
		forwardProp(props);
		props.remove(propNet.getInitProposition());
		return getStateFromBase(props, true);
	}

	private List<Move> getLegalMovesFromProps(Set<Component> props) {
		List<Move> totalMoves = new ArrayList<Move>();
		Random random = new Random();
		for (Role role : roles) {
			Set<Proposition> legals = propNet.getLegalPropositions().get(role);
			List<Move> moves = new ArrayList<Move>();
			for (Proposition prop : legals) {
				if (getPropValue(prop, props)) {
					moves.add(getMoveFromProposition(prop));
				}
			}
			totalMoves.add(moves.get(random.nextInt(moves.size())));
		}

		return totalMoves;
	}

	/**
	 * Computes the legal moves for role in state.
	 */
	@Override
	public List<Move> getLegalMoves(MachineState state, Role role)
			throws MoveDefinitionException {
		Set<Component> props = getProps(state);
		Set<Proposition> legals = propNet.getLegalPropositions().get(role);
		List<Move> moves = new ArrayList<Move>();
		for (Proposition prop : legals) {
			if (getPropValue(prop, props)) {
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
		Set<Component> props = getProps(state);
		updateState(props, moves);
		return getUpdatedState(props, true);
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
	public List<Component> getOrdering()
	{
		// List to contain the topological ordering.
		List<Component> order = new LinkedList<Component>();

		// All of the components in the PropNet
		List<Component> components = new ArrayList<Component>(propNet.getComponents());

		// All of the propositions in the PropNet.
		Stack<Component> stack = new Stack<Component>();

		// Mark all the vertices as not visited
		Map<Component, Boolean> visited = new HashMap<Component, Boolean>();
		for (Component c : components){
			visited.put(c, false);
		}

		// Call the recursive helper function to store
		// Topological Sort starting from all vertices
		// one by one
		Set<Component> tempVisited = new HashSet<Component>();
		for (Component c : components){
			if(!visited.get(c)){
				tempVisited.clear();
				topologicalSortUtil(c, visited, stack, tempVisited);
			}
		}
		// Print contents of stack
		while (!stack.empty()){
			Component c = stack.pop();
			if(c instanceof Proposition){
				Proposition p = (Proposition) c;
				if(p.getType() == Proposition.PropType.VIEW){
					order.add(c);
				}
			}
			else{
				order.add(c);
			}
		}
		return order;
	}

	void topologicalSortUtil(Component c, Map<Component,Boolean> visited, Stack<Component> stack, Set<Component> tempVisited)
	{
		// Mark the current node as visited.
		if (visited.get(c)) {
			return;
		}
		if (c instanceof Proposition) {
			Proposition p = (Proposition) c;
			if (p.getType() != Proposition.PropType.VIEW) {
				return;
			}
		}
		tempVisited.add(c);

		for (Component output : c.getOutputs())
		{
			topologicalSortUtil(output, visited, stack, tempVisited);
		}
		visited.put(c, true);
		tempVisited.remove(c);
		stack.push(c);
	}

	public void getInputProps(Component c, Set<Component> comps) {
		for (Component input : c.getInputs()) {
			if (input instanceof Proposition) {
				comps.add(input);
			}
			else {
				getInputProps(input, comps);
			}
		}
	}

	public Boolean verifySort() {
		Set<Component> seenComponents = new HashSet<Component>();
		for (Component c : ordering) {
			seenComponents.add(c);
			for (Component input : c.getInputs()) {
				if (input instanceof Proposition) {
					Proposition p = (Proposition) input;
					if (p.getType() != Proposition.PropType.VIEW) {
						continue;
					}
				}
				if (!seenComponents.contains(input)) {
					return false;
				}
			}
		}
		return true;
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

	/* Instead of returning a state, simply keeps it cached here.
	 * It returns true if the state is terminal.
	 */

	public void setIndex(int index, MachineState state) {
		Set<Component> props = getProps(state);
		threadSets.set(index, props);
	}

	public Boolean updateIndexRandomMove(int index) {
		Set<Component> props = threadSets.get(index);
		List<Move> moves = getLegalMovesFromProps(props);
		return updateSetIndexed(index, moves);
	}

	public Boolean updateSetIndexed(int index, List<Move> moves) {
		Set<Component> props = threadSets.get(index);
		MachineState state = getStateFromBase(props, false);
		updateState(props, moves);
		Boolean isTerminal = isTerminalProps(props);
		state = getStateFromBase(props, false);
		threadSets.set(index, props);
		return isTerminal;
	}

	private void updateState(Set<Component> props, List<Move> moves) {
		Set<Proposition> inputs = new HashSet<Proposition>();

		Map<GdlSentence, Proposition> map = propNet.getInputPropositions();
		List<GdlSentence> does = toDoes(moves);
		for (GdlSentence sentence : does) {
			inputs.add(map.get(sentence));
		}

		Map<Component, Boolean> newValues = new HashMap<Component, Boolean>();
		Stack<Component> toUpdate = new Stack<Component>();
		for (Proposition p : map.values()) {
			if (props.contains(p) != inputs.contains(p)) {
				newValues.put(p, inputs.contains(p));
				toUpdate.push(p);
			}
		}

		while(!toUpdate.isEmpty()) {
			Component nextUpdate = toUpdate.pop();
			Boolean newValue = newValues.get(nextUpdate);
			if (newValue == props.contains(nextUpdate)) {
				continue;
			}
			if (newValue) {
				props.add(nextUpdate);
			}
			else {
				props.remove(nextUpdate);
			}
			if (nextUpdate instanceof Proposition) {
				if (((Proposition) nextUpdate).getType() == Proposition.PropType.BASE) {
					continue;
				}
			}
			for (Component output : nextUpdate.getOutputs()) {
				if (output instanceof Proposition) {
					newValues.put(output, newValue);
					toUpdate.push(output);
				}
				else if (output instanceof And) {
					if (!newValue) {
						newValues.put(output, newValue);
						toUpdate.push(output);
					}
					else {
						if (!newValues.containsKey(output)) {
							newValues.put(output, propMarkConjunction(output, props));
							toUpdate.push(output);
						}
					}
				}
				else if (output instanceof Or) {
					if (newValue) {
						newValues.put(output, newValue);
						toUpdate.push(output);
					}
					else {
						if (!newValues.containsKey(output)) {
							newValues.put(output,  propMarkDisjunction(output, props));
							toUpdate.push(output);
						}
					}
				}
				else if (output instanceof Not) {
					newValues.put(output, !newValue);
					toUpdate.push(output);
				}
				else if (output instanceof Transition) {
					newValues.put(output,  newValue);
					toUpdate.push(output);
				}
			}
		}
	}

	public int getGoalIndexed(int index, Role role) throws GoalDefinitionException {
		return getGoalProps(role, threadSets.get(index));
	}

	public MachineState getUpdatedState(Set<Component> props, Boolean toCache) {
		Set<GdlSentence> contents = new HashSet<GdlSentence>();
		for (Proposition p : propNet.getBasePropositions().values())
		{
			if (props.contains(p))
			{
				contents.add(p.getName());
			}

		}
		MachineState newState = new MachineState(contents);
		if (toCache && cache != null) {
			cache.put(newState, props);
		}
		return newState;
	}

	/**
	 * A Naive implementation that computes a PropNetMachineState
	 * from the true BasePropositions.  This is correct but slower than more advanced implementations
	 * You need not use this method!
	 * @return PropNetMachineState
	 */
	public MachineState getStateFromBase(Set<Component> props, Boolean toCache)
	{
		Set<GdlSentence> contents = new HashSet<GdlSentence>();
		for (Proposition p : propNet.getBasePropositions().values())
		{
			if (props.contains(p.getSingleInput()))
			{
				contents.add(p.getName());
			}

		}
		MachineState newState = new MachineState(contents);
		if (toCache && cache != null) {
			cache.put(newState, props);
		}
		return newState;
	}

	public Boolean removeFromCache(MachineState state) {
		if (cache.containsKey(state)) {
			cache.remove(state);
			return true;
		}
		return false;
	}

	public void clearAllCache() {
		cache.clear();
	}
}