package disjointSet.fast;

import korat.finitization.IArraySet;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.impl.FinitizationFactory;

// DisjSetsFast class
//
// CONSTRUCTION: with int representing initial number of sets
//
// ******************PUBLIC OPERATIONS*********************
// void union( root1, root2 ) --> Merge two sets
// int find( x )              --> Return set containing x
// ******************ERRORS********************************
// No error checking is performed

/**
 * Disjoint set class, using union by rank
 * and path compression.
 * Elements in the set are numbered starting at 0.
 * @author Mark Allen Weiss
 */
public class DisjSetsFast  implements java.io.Serializable{
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;


    //@ invariant "s!=null && goodValues() && acyclic();    
     public boolean repOK() {
		 
	    return s!=null && goodValues() && acyclic(); 
	 }




	 //A Little MORE COMPLETE REPOK: it is not part of the original structure
     //public boolean repOK() {
         
       //  if(s!=null && s.length != 0 && allDiffSet()){return initial();}    
	  //	 return s!=null &&  correctMaximunHeight(s.length)  && correctHeight()  &&  balance() && goodValues() && acyclic();
	 //}



      private boolean correctMaximunHeight(int n) {
		 
		 int b =  ((int)(Math.log(n) / Math.log(2)) +  1) * (-1);
	     for( int i = 0; i < s.length; i++ ) {
	        	if(s[i] < 0 && s[i] < b) {
	        		return false;
	        	}

	     }
	     return true;
		 
	 }
	 


    public int numberOfchildren(int n) {
		 	int count = 0;
	        for( int i = 0; i < s.length; i++ ) {
	        	if(s[i] == n) {
	        		count ++;
	        	}
	        }
	        return count;
	 }
	 
	 public boolean balance() {
	        for( int i = 0; i < s.length; i++ ) {
	        	if(s[i]<0) {
	        		if (numberOfchildren(i) ==1)
	        			return s[i] == -2;
	        	}
	        }
	        return true;
	 }




	 public boolean allDiffSet() {
         for( int i = 0; i < s.length; i++ )
	        	if(s[i]>=0) {return false;}
	        return true;
	 }
	 
	 
      public boolean initial() {
	        for( int i = 0; i < s.length; i++ )
	        	
	        	if(s[i]!= -1) {return false;}
	        return true;
	  }
    

    /**
     * Construct the disjoint sets object.
     * @param numElements the initial number of disjoint sets.
     */
    public DisjSetsFast( int numElements ){
    	if(numElements<=0) {
    		throw new IllegalArgumentException();
    	}
    	
        s = new int [ numElements ];
        for( int i = 0; i < s.length; i++ )
            s[ i ] = -1;
    }

    
    private void assertIsRoot( int root )
    {
        assertIsItem( root );
        if( s[ root ] >= 0 )
            throw new IllegalArgumentException( "Union: " + root + " not a root" );
    }
    
    private void assertIsItem( int x )
    {
        if( x < 0 || x >= s.length )
            throw new IllegalArgumentException( "Disjoint sets: " + x + " not an item" );       
    }
    
    /**
     * Union two disjoint sets using the height heuristic.
     * For simplicity, we assume root1 and root2 are distinct
     * and represent set names.
     * @param root1 the root of set 1.
     * @param root2 the root of set 2.
     */
    //@ requires root1 >= 0 && root1 < s.length && root2 >=0 && root2 < s.length && root1 != root2 && s[root1] < 0 && s[root2] < 0;
    //@ ensures find(root1)==find(root2);
    public void union( int root1, int root2 ){
    	 assertIsRoot( root1 );
    	 assertIsRoot( root2 );
    	if( root1 == root2 )
    		throw new IllegalArgumentException( "Union: root1 == root2 " + root1 ); 

    	if( s[ root2 ] < s[ root1 ] )  // root2 is deeper
    		s[ root1 ] = root2;        // Make root2 new root
    	else{
    		if( s[ root1 ] == s[ root2 ] )
    			s[ root1 ]--;          // Update height if same
    		s[ root2 ] = root1;        // Make root1 new root
    	}

    }
	    
	    
	    
    private boolean goodValues() {
        boolean hasRoot = false;
        for (int i = 0; i < s.length; i++) {
            if (s[i] < 0 && s[i]>= 0-s.length) {
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
                while (s[currentIndex] >=0) {
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

    private boolean correctHeight(){
        for (int i = 0; i < s.length; i++) {
            if(s[i] <0){
                int x = heigth(i) * (-1);
                if (x < s[i])
                    return false;
            }    
        }
        return true;
    }


    private int heigth(int n){
    	if(isLeaf(n))
    		return 1;	
        int maxDepth = 0;

        for (int i = 0; i < s.length; i++) {
            if (s[i]==n){
            	maxDepth = Math.max(maxDepth, heigth(i));
                    
            }
        }
        return maxDepth + 1;
        
    
    }
    
    
    private boolean isLeaf(int n) {
        for (int i = 0; i < s.length; i++) {
        	if(s[i] == n) {
        		return false;
        	}
        	
        }
        return true;
        

    	
    }

    /**
     * Perform a find with path compression.
     * @param x the element being searched for.
     * @return the set containing x.
     */
    //@ requires x >= 0 && x < s.length;
    //@ ensures s[\result] < 0;
   public int Find(int x) {
       assertIsItem( x );
       return find(x);
    }

    
    
    
    private int find( int x )
    {
        if( s[ x ] < 0 )
            return x;
        else
            return s[ x ] = find( s[ x ] );
    }

    private int [ ] s;

    
    public static IFinitization finDisjSetsFast(int maxArrayLength) {
	    IFinitization f = FinitizationFactory.create(DisjSetsFast.class);
	    int max = maxArrayLength-1;
	    
	    IIntSet arrayLength = f.createIntSet(0, 1, max);
	    IIntSet elems = f.createIntSet((max*(-1)), 1, max);
	    IArraySet arrays = f.createArraySet(int[].class, arrayLength, elems, 1);
	    f.set("s", arrays);
	    return f;
}
    
    

    // Test main; all finds on same output line should be identical
  /*  public static void main( String [ ] args )
    {
        int NumElements = 128;
        int NumInSameSet = 16;

        DisjSetsFast ds = new DisjSetsFast( NumElements );
        int set1, set2;

        for( int k = 1; k < NumInSameSet; k *= 2 )
        {
            for( int j = 0; j + k < NumElements; j += 2 * k )
            {
                set1 = ds.find( j );
                set2 = ds.find( j + k );
                ds.union( set1, set2 );
            }
        }

        for( int i = 0; i < NumElements; i++ )
        {
            System.out.print( ds.find( i )+ "*" );
            if( i % NumInSameSet == NumInSameSet - 1 )
                System.out.println( );
        }
        System.out.println( );
    }*/
}
