package disjointSet.orig;

import korat.finitization.IArraySet;
import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

// DisjSets class
//
// CONSTRUCTION: with int representing initial number of sets
//
// ******************PUBLIC OPERATIONS*********************
// void union( root1, root2 ) --> Merge two sets
// int find( x )              --> Return set containing x
// ******************ERRORS********************************
//Error checking or parameters is performed

/**
 * Disjoint set class. (Package friendly so not used accidentally) Does not use
 * union heuristics or path compression. Elements in the set are numbered
 * starting at 0.
 * 
 * @author Mark Allen Weiss
 * @see DisjSetsFast
 */
public class DisjSets implements java.io.Serializable{
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	
	
  //@ invariant s!=null && goodValues() && acyclic();
	 public boolean repOK() {
		 return s!=null && goodValues() && acyclic();
	 }
	
	
   /**
     * Construct the disjoint sets object.
     * 
     * @param numElements
     *            the initial number of disjoint sets.
     */
    public DisjSets(int numElements) {
    	if(numElements<=0)
    		throw new IllegalArgumentException();
    	
        s = new int[numElements];
        for (int i = 0; i < s.length; i++)
            s[i] = -1;
    }

    /**
     * Union two disjoint sets. For simplicity, we assume root1 and root2 are
     * distinct and represent set names.
     * 
     * @param root1
     *            the root of set 1.
     * @param root2
     *            the root of set 2.
     */
    //@ requires root1 >= 0 && root1 < s.length && root2 >=0 && root2 < s.length && root1 != root2 && s[root1] == -1 && s[root2] == -1;
    //@ ensures find(root1)==find(root2);
    public void union(int root1, int root2) {
    	// assertIsRoot( root1 );
     //    assertIsRoot( root2 );
        if( root1 == root2 )
            throw new IllegalArgumentException( "Union: root1 == root2 " + root1 );
    	s[root2] = root1;
    }

    
    private void assertIsRoot( int root )
    {
        assertIsItem( root );
        if( s[ root ] != -1 )
            throw new IllegalArgumentException( "Union: " + root + " not a root" );
    }
    
    private void assertIsItem( int x )
    {
        if( x < 0 || x >= s.length )
            throw new IllegalArgumentException( "Disjoint sets: " + x + " not an item" );       
    }
    
    
    private boolean goodValues() {
        boolean hasRoot = false;
        for (int i = 0; i < s.length; i++) {
            if (s[i] == -1) {
                hasRoot = true;
            } else if (!((s[i] >= 0 && s[i] < s.length))) {
                return false;
            }
        }
        return hasRoot;
    }

    private boolean acyclic() {
        boolean[] visited = new boolean[s.length];
        for (int i = 0; i < visited.length; i++) {
            visited[i] = false;
        }
        int[] parents = new int[s.length];

        for (int i = 0; i < s.length; i++) {
            if (!visited[i]) {
                int numParents = 0;
                int currentIndex = i;
                while (s[currentIndex] != -1) {
                    for (int j = 0; j < numParents - 1; j++) {
                        if (parents[j] == s[currentIndex]) {
                            return false;
                        }
                    }
                    parents[numParents] = s[currentIndex];
                    numParents++;
                    visited[currentIndex] = true;
                    currentIndex = s[currentIndex];                    
                }
            }
        }
        return true;
    }

    /**
     * Perform a find. Error checks omitted again for simplicity.
     * 
     * @param x the element being searched for.
     * @return the set containing x.
     */
    //@ requires x >= 0 && x < s.length;
    //@ ensures s[\result] < 0;
    public int Find(int x) {
        assertIsItem( x );
        return find(x);
    }
    
    private int find(int x) {
        if (s[x] < 0)
            return x;
        else
            return find(s[x]);
    }

    private int[] s;
    
    public static IFinitization finDisjSets(int maxArrayLength) {
	    IFinitization f = FinitizationFactory.create(DisjSets.class);
	    
	    IIntSet arrayLength = f.createIntSet(0, 1, maxArrayLength-1);
	      IIntSet elems = f.createIntSet(-1, 1, maxArrayLength-1);

	    IArraySet arrays = f.createArraySet(int[].class, arrayLength, elems, 1);
	    f.set("s", arrays);
	    return f;
}

    // Test main; all finds on same output line should be identical
   /* public static void main(String[] args) {
        int numElements = 128;
        int numInSameSet = 16;

        DisjSets ds = new DisjSets(numElements);
        int set1, set2;

        for (int k = 1; k < numInSameSet; k *= 2) {
            for (int j = 0; j + k < numElements; j += 2 * k) {
                set1 = ds.find(j);
                set2 = ds.find(j + k);
                ds.union(set1, set2);
            }
        }
        System.out.println(ds.acyclic());

        for (int i = 0; i < numElements; i++) {
            System.out.print(ds.find(i) + "*");
            if (i % numInSameSet == numInSameSet - 1)
                System.out.println();
        }
        System.out.println();
    }*/
}
