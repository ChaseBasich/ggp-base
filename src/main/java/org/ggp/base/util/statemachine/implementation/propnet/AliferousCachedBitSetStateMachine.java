package org.ggp.base.util.statemachine.implementation.propnet;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
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
import org.ggp.base.util.statemachine.InternalMachineState;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;



public class AliferousCachedBitSetStateMachine extends StateMachine {
	/** The underlying proposition network  */
	private PropNet propNet;
	/** The topological ordering of the propositions */
	private List<Component> ordering;
	/** The ordering, but placed in an array for faster access*/
	private Component[] orderingArray;
	/** The player roles */
	private List<Role> roles;

	private Set<Move> goodInputs;

	//For faster traversal of the sets.
	private Proposition[] inputs;
	private Proposition[] bases;

	private Boolean factoring;

	//private Map<InternalMachineState, Set<Component> > cache;
	//private Map<InternalMachineState, BitSet> cacheBitSets;

	private ArrayList<Set<Component> > threadCache;

	private ArrayList<BitSet> threadBitSets;

	//private methods
	//mark the bases of the propnet
	private void markBases(MachineState state, Set<Component> baseSet) {
		if (state instanceof InternalMachineState) {
			InternalMachineState iState = (InternalMachineState) state;
			for (Proposition base : iState.getBases()) {
				baseSet.add(base);
			}
			return;
		}
		System.out.println("There is a big problem: state is not internal");
		Map<GdlSentence, Proposition> map = propNet.getBasePropositions();
		Set<GdlSentence> sentences = state.getContents();
		for (GdlSentence sentence : sentences) {
			Proposition p = map.get(sentence);
			baseSet.add(p);
		}

	}

	private void markActions(List<Move> moves, Set<Component> inputSet) {
		Map<GdlSentence, Proposition> map = propNet.getInputPropositions();
		List<GdlSentence> does = toDoes(moves);
		for (GdlSentence sentence : does) {
			inputSet.add(map.get(sentence));
		}
	}

	private Boolean propMarkNegation(Component c, Set<Component> props){
		return !props.contains(c.getSingleInput());
	}

	private Boolean propMarkConjunction(Component c, Set<Component> props){
		for ( Component component : c.getInputArray() )
		{
			if (!props.contains(component))
			{
				return false;
			}
		}
		return true;
	}

	private Boolean propMarkDisjunction(Component c, Set<Component> props){
		for ( Component component : c.getInputArray() )
		{
			if (props.contains(component) )
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
	private Boolean propValueNegation(Component c, Set<Component> props){
		return !getPropValue(c.getSingleInput(), props);
	}

	private Boolean propValueConjunction(Component c, Set<Component> props){
		for ( Component component : c.getInputArray() )
		{
			if (!getPropValue(component, props))
			{
				return false;
			}
		}
		return true;
	}

	private Boolean propValueDisjunction(Component c, Set<Component> props){
		for ( Component component : c.getInputArray() )
		{
			if (getPropValue(component, props))
			{
				return true;
			}
		}
		return false;
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
		for(Component p : orderingArray){
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
	 * Crystallizes all components in the propnet. This means the default java
	 * collection is transfered to an array and inputs and outputs can no longer be modified
	 */
	private void crystallize() {
		for (Component c : propNet.getComponents()) {
			c.crystallize();
		}
		inputs = new Proposition[propNet.getInputPropositions().values().size()];
		bases = new Proposition[propNet.getBasePropositions().values().size()];
		int i = 0;
		for (Proposition p : propNet.getInputPropositions().values()) {
			inputs[i] = p;
			p.setIndex(i);
			i++;
		}
		i = 0;
		for (Proposition p : propNet.getBasePropositions().values()) {
			bases[i] = p;
			p.setIndex(i);
			i++;
		}
	}

	private void crystallizeOrdering() {
		orderingArray = new Component[ordering.size()];
		int i = 0;
		for (Component c : ordering) {
			orderingArray[i] = c;
			i++;
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
			//cache = new HashMap<InternalMachineState, Set<Component> >();
			//cacheBitSets = new HashMap<InternalMachineState, BitSet>();
			threadCache = new ArrayList<Set<Component> >();
			threadBitSets = new ArrayList<BitSet>();
			propNet = OptimizingPropNetFactory.create(description);
			setTypes();
			roles = propNet.getRoles();
			for (int i = 0; i < 8; i++) {
				threadCache.add(new HashSet<Component>());
				threadBitSets.add(new BitSet());
			}
			goodInputs = new HashSet<Move>();
			if (roles.size() == 1) {
				numSubGames(roles.get(0));
				factoring = true;
			}
			else {
				factoring = false;
			}
			crystallize(); //freezes the propnet, no more changing components
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

	/**
	 * Computes if the state is terminal. Should return the value
	 * of the terminal proposition for the state.
	 */
	@Override
	public boolean isTerminal(MachineState state) {
		Set<Component> props = new HashSet<Component>();
		markBases(state, props);
		Boolean result = getPropValue(propNet.getTerminalProposition(), props);
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
		Set<Component> props = new HashSet<Component>();
		markBases(state, props);
		Set<Proposition> goals = propNet.getGoalPropositions().get(role);
		int count = 0;
		Proposition prop = null;
		//getPropMark(p, props)
		for(Proposition p : goals){
			if(getPropValue(p.getSingleInput(), props)){
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
	public InternalMachineState getInitialState() {
		Set<Component> props = new HashSet<Component>();
		props.add(propNet.getInitProposition());
		forwardProp(props);
		return getStateFromBase(props);
	}

	/**
	 * Computes the legal moves for role in state.
	 */
	@Override
	public List<Move> getLegalMoves(MachineState state, Role role)
			throws MoveDefinitionException {
		Set<Component> props = new HashSet<Component>();
		markBases(state, props);
		Set<Proposition> legals = propNet.getLegalPropositions().get(role);
		List<Move> moves = new ArrayList<Move>();
		for (Proposition prop : legals) {
			if (getPropValue(prop, props)) {
				if (factoring) {
					if (!goodInputs.contains(getMoveFromProposition(prop))) {
						continue;
					}
				}
				moves.add(getMoveFromProposition(prop));
			}
		}
		return moves;
	}

	public InternalMachineState updateThreadCache(MachineState state, List<Move> moves, int index, Boolean newSet) throws TransitionDefinitionException {
		InternalMachineState internalState = (InternalMachineState)state;
		if (!newSet) {
			Set<Component> prevProps = threadCache.get(index);
			BitSet prevBitSet = threadBitSets.get(index);
			BitSet intersection = new BitSet();
			intersection.or(prevBitSet);
			intersection.xor(internalState.getBitMask());
			Set<Component> newProps = getNextStateCached(internalState, moves, prevProps, intersection);
			InternalMachineState newState = getStateFromBase(newProps);
			threadCache.set(index, newProps);
			threadBitSets.set(index, internalState.getBitMask());
			return newState;
		}
		InternalMachineState newState;
		Set<Component> newProps;
		newProps = new HashSet<Component>();
		markBases(state, newProps);
		markActions(moves, newProps);
		forwardProp(newProps);
		newState = getStateFromBase(newProps);
		threadCache.set(index, newProps);
		threadBitSets.set(index, internalState.getBitMask());
		return newState;
	}

	private Set<Component> getNextStateCached(InternalMachineState state, List<Move> moves, Set<Component> prevProps, BitSet intersection)
			throws TransitionDefinitionException {
		Queue<Component> toUpdate = new LinkedList<Component>();
		Set<Component> newProps = new HashSet<Component>(prevProps);

		Set<Component> props = new HashSet<Component>();
		markActions(moves, props);

		for (Component input : inputs) {
			if (props.contains(input) && !prevProps.contains(input)) {
				newProps.add(input);
				for (Component o : input.getOutputArray()) {
					toUpdate.add(o);
				}
			}
			else if (!props.contains(input) && prevProps.contains(input)) {
				newProps.remove(input);
				for (Component o : input.getOutputArray()) {
					toUpdate.add(o);
				}
			}
		}

		BitSet stateBitMask = state.getBitMask();

		for (int i = intersection.nextSetBit(0); i >= 0; i = intersection.nextSetBit(i+1)) {

			Component base = bases[i];
			for (Component o : base.getOutputArray()) {
				toUpdate.add(o);
			}
			if (stateBitMask.get(i)) {
				newProps.add(base);
			}
			else {
				newProps.remove(base);
			}
		    if (i == Integer.MAX_VALUE) {
		        break; // or (i+1) would overflow
		    }
		}

		while(!toUpdate.isEmpty()) {
			Component c = toUpdate.poll();
			Boolean newValue = false;

			if (c instanceof Proposition) {
				Proposition p = (Proposition) c;
				if (!isViewProp(p)) {
					continue;
				}
				newValue = newProps.contains(p.getSingleInput());
			}
			else if (c instanceof And) {
				newValue = propMarkConjunction(c, newProps);
			}
			else if (c instanceof Not) {
				newValue = !newProps.contains(c.getSingleInput());
			}
			else if (c instanceof Or) {
				newValue = propMarkDisjunction(c, newProps);
			}
			else if (c instanceof Transition) {
				newValue = newProps.contains(c.getSingleInput());
			}

			if (newValue && !newProps.contains(c)) {
				newProps.add(c);
				for (Component o : c.getOutputArray()) {
					toUpdate.add(o);
				}
			}
			else if (!newValue && newProps.contains(c)) {
				newProps.remove(c);
				for (Component o : c.getOutputArray()) {
					toUpdate.add(o);
				}
			}
		}
		return newProps;
	}

	/**
	 * Computes the next state given state and the list of moves.
	 */
	@Override
	public MachineState getNextState(MachineState state, List<Move> moves)
			throws TransitionDefinitionException {
		InternalMachineState internalState = (InternalMachineState)state;
		Set<Component> props = new HashSet<Component>();
		markBases(internalState, props);
		markActions(moves, props);
		forwardProp(props);
		InternalMachineState newState = getStateFromBase(props);
		return newState;
	}

	private void findInputs(Proposition goal, Set<Move> inputSet) {
		Set<Component> seen = new HashSet<Component>();
		Queue<Component> toExplore = new LinkedList<Component>();
		toExplore.add(goal);
		while(!toExplore.isEmpty()) {
			Component c = toExplore.poll();
			for (Component input : c.getInputs()) {
				if (seen.contains(input)) {
					continue;
				}
				if (input instanceof Proposition) {
					Proposition p = (Proposition) input;
					if ((p.getType() == Proposition.PropType.INPUT)) {
						inputSet.add(getMoveFromProposition(p));
						continue;
					}
				}
				toExplore.add(input);
				seen.add(input);
			}
		}
	}

	public int numSubGames(Role role) {
		Set<Proposition> goals = propNet.getGoalPropositions().get(role);
		Set<Proposition> removedGoals = new HashSet<Proposition>();
		factoring = true;
		Set<Proposition> newGoals = new HashSet<Proposition>();
		for (Proposition goal : goals) {
			if (getGoalValue(goal) == 0) {
				continue;
			}
			Component goalInput = goal.getSingleInput();
			if (goalInput instanceof Or) {
				for (Component c : goalInput.getInputs()) {
					Proposition newGoal = new Proposition(goal.getName());
					newGoal.addInput(c);
					c.removeOutput(goalInput);
					c.addOutput(newGoal);
					for(Component output : goal.getOutputs()) {
						newGoal.addOutput(output);
					}
					newGoals.add(newGoal);
					propNet.addComponent(newGoal);
				}
				propNet.removeComponent(goalInput);
				goalInput.removeOutput(goal);
				goal.removeInput(goalInput);
				removedGoals.add(goal);
			}
		}
		for (Proposition goal : removedGoals) {
			propNet.removeComponent(goal);
			goals.remove(goal);
		}
		goals.addAll(newGoals);

		int maxScore = 1;
		Proposition bestGoal = null;

		for (Proposition goal : goals) {
			int goalValue = getGoalValue(goal);
			if (goalValue < maxScore) {
				continue;
			}
			maxScore = getGoalValue(goal);
			Set<Move> inputSet = new HashSet<Move>();
			findInputs(goal, inputSet);
			bestGoal = goal;
			goodInputs = inputSet;
		}

		return newGoals.size();
	}

	/**
	 * This should compute the topological ordering of propositions.
	 * Each component is either a proposition, logical gate, or transition.
	 * Logical gates and transitions only have propositions as inputs.
	 *
	 * The base propositions and input propositions should always be exempt
	 * from this ordering.
	 *
	 * The base propositions values are set from the InternalMachineState that
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

		for (Component output : c.getOutputArray())
		{
			topologicalSortUtil(output, visited, stack, tempVisited);
		}
		visited.put(c, true);
		tempVisited.remove(c);
		stack.push(c);
	}

	public void getInputProps(Component c, Set<Component> comps) {
		for (Component input : c.getInputArray()) {
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
			for (Component input : c.getInputArray()) {
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
		crystallizeOrdering();
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

	/**
	 * A Naive implementation that computes a PropNetInternalMachineState
	 * from the true BasePropositions.  This is correct but slower than more advanced implementations
	 * You need not use this method!
	 * @return PropNetInternalMachineState
	 */
	public InternalMachineState getStateFromBase(Set<Component> props)
	{
		ArrayList<Proposition> stateBases = new ArrayList<Proposition>();
		BitSet bitMask = new BitSet(bases.length);
		for (Proposition p : bases)
		{
			if (props.contains(p.getSingleInput()))
			{
				stateBases.add(p);
				bitMask.set(p.getIndex());
			}
		}
		Proposition[] baseArray = new Proposition[stateBases.size()];
		InternalMachineState state = new InternalMachineState(stateBases.toArray(baseArray), bitMask);
		return state;
	}

	public void removeFromCache(MachineState state) {
		//cache.remove((InternalMachineState)state);
		//cacheBitSets.remove((InternalMachineState)state);
	}

	public void clearCache() {
		//cache.clear();
	//	cacheBitSets.clear();
	}
}