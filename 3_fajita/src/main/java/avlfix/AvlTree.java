package avlfix;
import java.util.HashSet;
import java.util.LinkedList;
//import java.util.LinkedList;
import java.util.Set;

import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

/**
 * @Invariant all x: AvlNode | x in this.root.*(left @+ right) @- null => 
 * (
 *		(x !in x.^(left @+ right)) && 
 *		(all y: AvlNode | (y in x.left.*(left @+ right) @-null) => y.data < x.data ) && 
 *		(all y: AvlNode | (y in x.right.*(left @+right) @- null) => x.data < y.data ) && 
 *		(x.left=null && x.right=null => 
 *				x.height=0) && 
 *		(x.left=null && x.right!=null => 
 *				x.height=1 && x.right.height=0) && 
 *		(x.left!=null && x.right=null => 
 *				x.height=1 && x.left.height=0) && 
 *		(x.left!=null && x.right!=null => 
 *				x.height= (x.left.height>x.right.height ? 
 *		x.left.height : x.right.height )+1 && ( 
 *		(x.left.height > x.right.height ? 
 *		x.left.height - x.right.height : 
 *		x.right.height - x.left.height ))<=1));
 */
public class AvlTree implements java.io.Serializable {


	/**
	 * 
	 */
	private static final long serialVersionUID = -5895395786986876938L;

	private  AvlNode root;

	private int size;

	/***Breadth first KORAT-TUNNEADO*/
	public boolean repOK() {
        // checks that empty tree has size zero
        if (root == null)
            return size == 0;
        // checks that the input is a tree
          if (!isAcyclic())
            return false;
        // checks that data is ordered
        if (!isOrdered(root))
            return false;
        // checks that size is consistent
        if (numNodes(root) != size)
            return false;
        if(!isBalanced())
        	return false;
        return true;
    }
	
	private boolean isBalanced(){
		LinkedList<AvlNode> queue = new LinkedList<AvlNode>();
		queue.add(root);
        while (!queue.isEmpty()) {
            AvlNode current = (AvlNode) queue.removeFirst();
            // BUG in repOK: height of null should be -1;
            //int l_Height = current.left == null ? 0 : current.left.height;
            //int r_Height = current.right == null ? 0 : current.right.height;
			int l_Height = current.left == null ? -1 : current.left.height;
			int r_Height = current.right == null ? -1 : current.right.height;
			int difference = l_Height - r_Height;
			if (difference < -1 || difference > 1)
				return false; // Not balanced.
			int max = l_Height > r_Height ? l_Height : r_Height;
			if (current.height != 1 + max)
				return false; // Wrong height.
            if (current.left != null) {
            	queue.add(current.left);
            }
            if (current.right != null) {
            	queue.add(current.right);
            }
        }
        return true;

		
	}
        
  	private boolean isAcyclic() {
          Set<AvlNode> visited = new HashSet<AvlNode>();
          visited.add(root);
          LinkedList<AvlNode> workList = new LinkedList<AvlNode>();
          workList.add(root);
          while (!workList.isEmpty()) {
              AvlNode current = (AvlNode) workList.removeFirst();
              if (current.left != null) {
                  // checks that the tree has no cycle
                  if (!visited.add(current.left))
                      return false;
                  workList.add(current.left);
              }
              if (current.right != null) {
                  // checks that the tree has no cycle
                  if (!visited.add(current.right))
                      return false;
                  workList.add(current.right);
              }
          }
          return true;
      }
	
	   private int numNodes(AvlNode n) {
 	        if (n == null)
 	            return 0;
 	        return 1 + numNodes(n.left) + numNodes(n.right);
 	    }
	   
	  	 private boolean isOrdered(AvlNode n) {
	         return isOrdered(n, -1, -1);
	     }

	     private boolean isOrdered(AvlNode n, int min, int max) {
	         // if (n.info == null)
	         // return false;
	         if (n.data == -1)
	             return false;
	         // if ((min != null && n.info.compareTo(min) <= 0)
	         // || (max != null && n.info.compareTo(max) >= 0))
	         if ((min != -1 && n.data <= (min)) || (max != -1 && n.data >= (max)))

	             return false;
	         if (n.left != null)
	             if (!isOrdered(n.left, min, n.data))
	                 return false;
	         if (n.right != null)
	             if (!isOrdered(n.right, n.data, max))
	                 return false;
	         return true;
	     }

	
/**************************Finitizaion**************************************/
	
	public static IFinitization finAvlTree(int maxSize) {
		return finAvlTree(maxSize, maxSize, 0, maxSize -1);
	}

	/**To generate AvlTrees that have a given number of nodes, the Korat
search algorithm uses the finitization method.
In this method we specify bounds on the number of objects to be used to 
construct instances of the data structure, as well as possible values 
stored in the fields of those objects.
	 */
	public static IFinitization finAvlTree(int numAvlNode, int maxSize, int minKey, int maxKey) {

		IFinitization f = FinitizationFactory.create(AvlTree.class);

		IObjSet entry = f.createObjSet(AvlNode.class,numAvlNode);
		entry.setNullAllowed(true);
		IClassDomain entryClassDomain = f.createClassDomain(AvlNode.class);
		entry.addClassDomain(entryClassDomain);
		entryClassDomain.includeInIsomorphismCheck(true);


		IIntSet sizes = f.createIntSet(0, maxSize);

		IIntSet height = f.createIntSet(minKey, maxKey);

		IObjSet elems = f.createObjSet(Integer.class);
		IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
			elemsClassDomain.includeInIsomorphismCheck(false);
		for (int i = minKey; i <= maxKey; i++)
			elemsClassDomain.addObject(new Integer(i));
		elems.addClassDomain(elemsClassDomain);
		elems.setNullAllowed(false); //not null allowed

		f.set("root", entry);
		f.set("size", sizes);
		f.set(AvlNode.class, "data", elems);
		f.set("AvlNode.height", height);        
		f.set("AvlNode.left", entry);
		f.set("AvlNode.right", entry);

		return f;

	}

		
	/*********************Class Methods*************************************/
	
	
	
	// Pablo: Implementation of methods from Mark Allen Weiss. repOK from roops.
	/**
	 * Implements an AVL tree.
	 * Note that all "matching" is based on the compareTo method.
	 * @author Mark Allen Weiss
	 */
    /**
     * Construct the tree.
     */
    public AvlTree( )
    {
        root = null;
    }

    /**
     * Insert into the tree; duplicates are ignored.
     * @param x the item to insert.
     */
    public void insert( int x )
    {
        root = insert( x, root );
    }

    /**
     * Find the smallest item in the tree.
     * @return smallest item or null if empty.
     */
    public int findMin( )
    {
        if( isEmpty( ) )
            throw new RuntimeException("Underflow");
        return findMin( root ).data;
    }

    /**
     * Find the largest item in the tree.
     * @return the largest item of null if empty.
     */
    public int findMax( )
    {
        if( isEmpty( ) )
            throw new RuntimeException("Underflow");
        return findMax( root ).data;
    }

    /**
     * Find an item in the tree.
     * @param x the item to search for.
     * @return true if x is found.
     */
    public boolean contains( int x )
    {
        return contains( x, root );
    }

    /**
     * Make the tree logically empty.
     */
    public void makeEmpty( )
    {
        root = null;
    }

    /**
     * Test if the tree is logically empty.
     * @return true if empty, false otherwise.
     */
    public boolean isEmpty( )
    {
        return root == null;
    }

    /**
     * Print the tree contents in sorted order.
     */
    public void printTree( )
    {
        if( isEmpty( ) )
            System.out.println( "Empty tree" );
        else
            printTree( root );
    }

    private static final int ALLOWED_IMBALANCE = 1;
    
    // Assume t is either balanced or within one of being balanced
    private AvlNode balance( AvlNode t )
    {
        if( t == null )
            return t;
        
        if( height( t.left ) - height( t.right ) > ALLOWED_IMBALANCE )
            if( height( t.left.left ) >= height( t.left.right ) )
                t = rotateWithLeftChild( t );
            else
                t = doubleWithLeftChild( t );
        else
        if( height( t.right ) - height( t.left ) > ALLOWED_IMBALANCE )
            if( height( t.right.right ) >= height( t.right.left ) )
                t = rotateWithRightChild( t );
            else
                t = doubleWithRightChild( t );

        t.height = Math.max( height( t.left ), height( t.right ) ) + 1;
        return t;
    }
    
    public void checkBalance( )
    {
        checkBalance( root );
    }
    
    private int checkBalance( AvlNode t )
    {
        if( t == null )
            return -1;
        
        if( t != null )
        {
            int hl = checkBalance( t.left );
            int hr = checkBalance( t.right );
            if( Math.abs( height( t.left ) - height( t.right ) ) > 1 ||
                    height( t.left ) != hl || height( t.right ) != hr )
                System.out.println( "OOPS!!" );
        }
        
        return height( t );
    }
    
    
    /**
     * Internal method to insert into a subtree.
     * @param x the item to insert.
     * @param t the node that roots the subtree.
     * @return the new root of the subtree.
     */
    private AvlNode insert( Integer x, AvlNode t )
    {
        if( t == null ) {
        	size++;
            return new AvlNode( x );
        }
        
        int compareResult = x.compareTo( t.data );
        
        if( compareResult < 0 )
            t.left = insert( x, t.left );
        else if( compareResult > 0 )
            t.right = insert( x, t.right );
        else
            ;  // Duplicate; do nothing
        return balance( t );
    }

    /**
     * Internal method to find the smallest item in a subtree.
     * @param t the node that roots the tree.
     * @return node containing the smallest item.
     */
    private AvlNode findMin( AvlNode t )
    {
        if( t == null )
            return t;

        while( t.left != null )
            t = t.left;
        return t;
    }

    /**
     * Internal method to find the largest item in a subtree.
     * @param t the node that roots the tree.
     * @return node containing the largest item.
     */
    private AvlNode findMax( AvlNode t )
    {
        if( t == null )
            return t;

        while( t.right != null )
            t = t.right;
        return t;
    }

    /**
     * Internal method to find an item in a subtree.
     * @param x is item to search for.
     * @param t the node that roots the tree.
     * @return true if x is found in subtree.
     */
    private boolean contains( Integer x, AvlNode t )
    {
        while( t != null )
        {
            int compareResult = x.compareTo( t.data );
            
            if( compareResult < 0 )
                t = t.left;
            else if( compareResult > 0 )
                t = t.right;
            else
                return true;    // Match
        }

        return false;   // No match
    }

    /**
     * Internal method to print a subtree in sorted order.
     * @param t the node that roots the tree.
     */
    private void printTree( AvlNode t )
    {
        if( t != null )
        {
            printTree( t.left );
            System.out.println( t.data );
            printTree( t.right );
        }
    }

    /**
     * Return the height of node t, or -1, if null.
     */
    private int height( AvlNode t )
    {
        return t == null ? -1 : t.height;
    }

    /**
     * Rotate binary tree node with left child.
     * For AVL trees, this is a single rotation for case 1.
     * Update heights, then return new root.
     */
    private AvlNode rotateWithLeftChild( AvlNode k2 )
    {
        AvlNode k1 = k2.left;
        k2.left = k1.right;
        k1.right = k2;
        k2.height = Math.max( height( k2.left ), height( k2.right ) ) + 1;
        k1.height = Math.max( height( k1.left ), k2.height ) + 1;
        return k1;
    }

    /**
     * Rotate binary tree node with right child.
     * For AVL trees, this is a single rotation for case 4.
     * Update heights, then return new root.
     */
    private AvlNode rotateWithRightChild( AvlNode k1 )
    {
        AvlNode k2 = k1.right;
        k1.right = k2.left;
        k2.left = k1;
        k1.height = Math.max( height( k1.left ), height( k1.right ) ) + 1;
        k2.height = Math.max( height( k2.right ), k1.height ) + 1;
        return k2;
    }

    /**
     * Double rotate binary tree node: first left child
     * with its right child; then node k3 with new left child.
     * For AVL trees, this is a double rotation for case 2.
     * Update heights, then return new root.
     */
    private AvlNode doubleWithLeftChild( AvlNode k3 )
    {
        k3.left = rotateWithRightChild( k3.left );
        return rotateWithLeftChild( k3 );
    }

    /**
     * Double rotate binary tree node: first right child
     * with its left child; then node k1 with new right child.
     * For AVL trees, this is a double rotation for case 3.
     * Update heights, then return new root.
     */
    private AvlNode doubleWithRightChild( AvlNode k1 )
    {
        k1.right = rotateWithLeftChild( k1.right );
        return rotateWithRightChild( k1 );
    }



}

