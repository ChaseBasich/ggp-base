package org.ggp.base.util.propnet.architecture;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

/**
 * The root class of the Component hierarchy, which is designed to represent
 * nodes in a PropNet. The general contract of derived classes is to override
 * all methods.
 */

public abstract class Component implements Serializable
{

	private static final long serialVersionUID = 352524175700224447L;
    /** The inputs to the component. */
    private final Set<Component> inputs;
    /** The outputs of the component. */
    private final Set<Component> outputs;


    //Arrays for faster traversal
    private Component inputArray[];

    private Component outputArray[];

    private Boolean crystallized;

    /**
     * Creates a new Component with no inputs or outputs.
     */
    public Component()
    {
        this.inputs = new HashSet<Component>();
        this.outputs = new HashSet<Component>();
        crystallized = false;
    }

    /**
     * Adds a new input.
     *
     * @param input
     *            A new input.
     * @throws CrystallizedComponentException
     */
    public void addInput(Component input)
    {
    	if (crystallized) {
    		System.out.println("Component already crystallized, not adding input");
    		return;
    	}
        inputs.add(input);
    }

    public void removeInput(Component input)
    {
    	if (crystallized) {
    		System.out.println("Component already crystallized, not removing input");
    		return;
    	}
    	inputs.remove(input);
    }

    public void removeOutput(Component output)
    {
    	if (crystallized) {
    		System.out.println("Component already crystallized, not removing output");
    		return;
    	}
    	outputs.remove(output);
    }

    public void removeAllInputs()
    {
    	if (crystallized) {
    		System.out.println("Component already crystallized, not removing inputs");
    		return;
    	}
		inputs.clear();
	}

	public void removeAllOutputs()
	{
		if (crystallized) {
    		System.out.println("Component already crystallized, not removing outputs");
    		return;
    	}
		outputs.clear();
	}

    /**
     * Adds a new output.
     *
     * @param output
     *            A new output.
     */
    public void addOutput(Component output)
    {
    	if (crystallized) {
    		System.out.println("Component already crystallized, not adding output");
    		return;
    	}
        outputs.add(output);
    }

    /**
     * Getter method.
     *
     * @return The inputs to the component.
     */
    public Set<Component> getInputs()
    {
        return inputs;
    }

    /**
     * A convenience method, to get a single input.
     * To be used only when the component is known to have
     * exactly one input.
     *
     * @return The single input to the component.
     */
    public Component getSingleInput() {
        assert inputs.size() == 1;
        if (crystallized) {
        	return inputArray[0];
        }
        return inputs.iterator().next();
    }

    /**
     * Getter method.
     *
     * @return The outputs of the component.
     */
    public Set<Component> getOutputs()
    {
        return outputs;
    }

    /**
     * A convenience method, to get a single output.
     * To be used only when the component is known to have
     * exactly one output.
     *
     * @return The single output to the component.
     */
    public Component getSingleOutput() {
        assert outputs.size() == 1;
        if (crystallized) {
        	return outputArray[0];
        }
        return outputs.iterator().next();
    }

    /**
     * Returns the value of the Component.
     *
     * @return The value of the Component.
     */
    public abstract boolean getValue();

    /**
     * Returns a representation of the Component in .dot format.
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public abstract String toString();

    /**
     * Returns a configurable representation of the Component in .dot format.
     *
     * @param shape
     *            The value to use as the <tt>shape</tt> attribute.
     * @param fillcolor
     *            The value to use as the <tt>fillcolor</tt> attribute.
     * @param label
     *            The value to use as the <tt>label</tt> attribute.
     * @return A representation of the Component in .dot format.
     */
    protected String toDot(String shape, String fillcolor, String label)
    {
        StringBuilder sb = new StringBuilder();

        sb.append("\"@" + Integer.toHexString(hashCode()) + "\"[shape=" + shape + ", style= filled, fillcolor=" + fillcolor + ", label=\"" + label + "\"]; ");
        for ( Component component : getOutputs() )
        {
            sb.append("\"@" + Integer.toHexString(hashCode()) + "\"->" + "\"@" + Integer.toHexString(component.hashCode()) + "\"; ");
        }

        return sb.toString();
    }

    public void crystallize() {
    	crystallized = true;
    	inputArray = new Component[inputs.size()];
    	outputArray = new Component[outputs.size()];
    	int i = 0;
    	for (Component c : inputs) {
    		inputArray[i] = c;
    		i++;
    	}
    	i = 0;
    	for (Component c : outputs) {
    		outputArray[i] = c;
    		i++;
    	}
    }

    public Component[] getInputArray() {
    	return inputArray;
    }

    public Component[] getOutputArray() {
    	return outputArray;
    }

}