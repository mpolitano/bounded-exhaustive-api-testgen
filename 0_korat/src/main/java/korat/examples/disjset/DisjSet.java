package korat.examples.disjset;

import java.io.Serializable;
import java.util.BitSet;

import korat.finitization.IArraySet;
import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

/**
 * DisjSet: disjoint set implementation took from Korat. 
 * Added builders:
 *     - DisjSet()
 *     - union(int value)
 */
public class DisjSet implements Serializable {

    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	// helper class
    public static class Record implements Serializable  {

        /**
		 * 
		 */
		private static final long serialVersionUID = 1L;

		public int parent;

        public int rank;

        public Record() {

        }

        public Record(Record rec) {
            parent = rec.parent;
            rank = rec.rank;
        }

    }

    // end of helper class

    private Record[] elements;

    private int size;

    private static final int MAX_SIZE=30;
    
    /*
     * Builders ---------------------------
     */
    public DisjSet(int n) {
        if (n < 1 || n > MAX_SIZE)
            throw new IllegalArgumentException("The int n should be greater than 0 and less than "+MAX_SIZE);
        elements = new Record[n];
        size = n;
        makeSet();
    }
    
    private void makeSet() {
        for (int i=0; i<size; i++)
        {
            // Initially, all elements are in
            // their own set.
            elements[i] = new Record();
            elements[i].parent = i;
        }
    }
    
    // Returns representative of x's set
    private int find(int x) {
        // Finds the representative of the set
        // that x is an element of
        if (elements[x].parent!=x) {
            // if x is not the parent of itself
            // Then x is not the representative of
            // his set,
            elements[x].parent = find(elements[x].parent);
 
            // so we recursively call Find on its parent
            // and move i's node directly under the
            // representative of this set
        }
 
        return elements[x].parent;
    }
    
    // Unites the set that includes x and the set
    // that includes x
    public void union(int x, int y) {
        // Find representatives of two sets
        int xRoot = find(x), yRoot = find(y);
 
        // Elements are in the same set, no need
        // to unite anything.
        if (xRoot == yRoot)
            return;
 
         // If x's rank is less than y's rank
        if (elements[xRoot].rank < elements[yRoot].rank)
 
            // Then move x under y  so that depth
            // of tree remains less
            elements[xRoot].parent = yRoot;
 
        // Else if y's rank is less than x's rank
        else if (elements[yRoot].rank < elements[xRoot].rank)
 
            // Then move y under x so that depth of
            // tree remains less
            elements[yRoot].parent = xRoot;
 
        else // if ranks are the same
        {
            // Then move y under x (doesn't matter
            // which one goes where)
            elements[yRoot].parent = xRoot;
 
            // And increment the the result tree's
            // rank by 1
            elements[xRoot].rank = elements[xRoot].rank + 1;
        }
    }
    /*
     * -----------------------------------------
     */

    public boolean allDifferent() {
        int n = size - 1;
        // for (int n = 1; n < size; n++) // generates fewer candidates, but
        // slower
        for (int i = 0; i < n; i++)
            for (int j = i + 1; j <= n; j++)
                if (elements[i] == elements[j])
                    return false;
        return true;
    }

    // methods used by Korat
    public boolean repOK() {

        if (elements.length != size)
            return false;

        if (!allDifferent())
            return false;

        int numRoots = 0, numElRankZero = 0;
        BitSet seenParent = new BitSet(size);
        for (int i = 0; i < size; i++) {
            int parentID = elements[i].parent;
            if (parentID < 0 || parentID >= size)
                return false;
            if (parentID != i) {
                int parentRank = elements[parentID].rank;
                if (parentRank <= elements[i].rank)
                    return false;
                if (elements[i].rank == parentRank - 1)
                    seenParent.set(parentID);
            } else
                numRoots += 1;
        }

        for (int i = 0; i < size; i++)
            if (!seenParent.get(i) && elements[i].rank == 0)
                numElRankZero += 1;

        if (numRoots > numElRankZero)
            return false;

        return true;
    }
    
    public static IFinitization finDisjSet(int size) {

        IFinitization f = FinitizationFactory.create(DisjSet.class);

        IClassDomain bindingsCD = f.createClassDomain(Record.class, size);
        IObjSet bindings = f.createObjSet(Record.class);
        bindings.addClassDomain(bindingsCD);

        IIntSet lens = f.createIntSet(0, size);
        IArraySet elems = f.createArraySet(Record[].class, lens, bindings, 1);

        f.set("size", f.createIntSet(0, size));
        f.set(Record.class, "parent", f.createIntSet(0, size - 1));
        f.set(Record.class, "rank", f.createIntSet(0, size - 1));
        f.set("elements", elems);

        return f;

    }
}
