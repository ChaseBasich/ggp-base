package org.ggp.base.util.statemachine;

import java.util.BitSet;

import org.ggp.base.util.propnet.architecture.components.Proposition;

public class InternalMachineState extends MachineState {

	Proposition[] bases;

	BitSet bitMask;

	public InternalMachineState(Proposition[] newBases, BitSet newBitMask) {
		bases = newBases;
		bitMask = newBitMask;
	}

	public Proposition[] getBases() {
		return bases;
	}

	public Proposition getBase(int index) {
		if (index < bases.length) {
			return bases[index];
		}
		else {
			System.out.println("Error, index out of range, returning null");
			return null;
		}
	}

	public BitSet getBitMask() {
		return bitMask;
	}

	@Override
	public InternalMachineState clone() {
		return new InternalMachineState(bases.clone(), (BitSet) bitMask.clone());
	}

	/* Utility methods */
    @Override
	public int hashCode()
    {
        return bitMask.hashCode();
    }

    @Override
	public String toString()
    {
    	String str = new String();
    	for (Proposition base : bases) {
    		str += base.toString();
    	}
    	return str;
    }

    @Override
	public boolean equals(Object o)
    {
        if ((o != null) && (o instanceof InternalMachineState))
        {
            InternalMachineState state = (InternalMachineState) o;
            return state.getBitMask().equals(bitMask);
        }

        return false;
    }

}
