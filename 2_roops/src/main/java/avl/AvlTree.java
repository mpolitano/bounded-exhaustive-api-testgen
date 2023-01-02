package avl;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

//$category roops.core.objects

//Authors: Marcelo Frias
//$benchmarkclass
/**
 * @Invariant all x: AvlNode | x in this.root.*(left @+ right) @- null => 
 * (
 *		(x !in x.^(left @+ right)) && 
 *		(all y: AvlNode | (y in x.left.*(left @+ right) @-null) => y.element < x.element ) && 
 *		(all y: AvlNode | (y in x.right.*(left @+right) @- null) => x.element < y.element ) && 
 *		(x.left=null && x.right=null => x.height=0) && 
 *		(x.left=null && x.right!=null => x.height=1 && x.right.height=0) && 
 *		(x.left!=null && x.right=null => x.height=1 && x.left.height=0) && 
 *		(x.left!=null && x.right!=null => x.height= (x.left.height>x.right.height ? x.left.height : x.right.height )+1 && ( (x.left.height > x.right.height ? x.left.height - x.right.height : x.right.height - x.left.height ))<=1)
 * );
 * 
 */
public class AvlTree implements java.io.Serializable{

	/**
	 * 
	 */
	private static final long serialVersionUID = -5981818427258375961L;
	/*@ nullable @*/AvlNode root;
	
	
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
     * Remove from the tree. Nothing is done if x is not found.
     * @param x the item to remove.
     */
    public void remove( int x )
    {
        root = remove( x, root );
    }

       
    /**
     * Internal method to remove from a subtree.
     * @param x the item to remove.
     * @param t the node that roots the subtree.
     * @return the new root of the subtree.
     */
    private AvlNode remove( Integer x, AvlNode t )
    {
        if( t == null )
            return t;   // Item not found; do nothing
            
        int compareResult = x.compareTo( t.element );
            
        if( compareResult < 0 )
            t.left = remove( x, t.left );
        else if( compareResult > 0 )
            t.right = remove( x, t.right );
        else if( t.left != null && t.right != null ) // Two children
        {
            t.element = findMin( t.right ).element;
            t.right = remove( t.element, t.right );
        }
        else
            t = ( t.left != null ) ? t.left : t.right;
        return balance( t );
    }
    
    /**
     * Find the smallest item in the tree.
     * @return smallest item or null if empty.
     */
    public int findMin( )
    {
        if( isEmpty( ) )
            throw new RuntimeException("Underflow");
        return findMin( root ).element;
    }

    /**
     * Find the largest item in the tree.
     * @return the largest item of null if empty.
     */
    public int findMax( )
    {
        if( isEmpty( ) )
            throw new RuntimeException("Underflow");
        return findMax( root ).element;
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
        if( t == null )
            return new AvlNode( x );
        
        int compareResult = x.compareTo( t.element );
        
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
            int compareResult = x.compareTo( t.element );
            
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
            System.out.println( t.element );
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

	
	


	
	
    //if (root.color == RED)
    //   return false;    

	//*************************************************************************
	//************** From now on repOk()  *************************************
	//*************************************************************************

    public boolean repOK() { 
	Set allNodes = new HashSet();
	List allData = new ArrayList();
	Stack stack = new Stack();
	if (root != null) {
              stack.push(root);
            }
	
	while (stack.size()>0) {

		AvlNode node = (AvlNode) stack.pop();

		if (!allNodes.add(node))
			return false; // Not acyclic.

    //BUG FIX:this is no part of original repOK() from Roops
    //BUG in repOK:// Repeated data.;
		if (!allData.add(node.element))
			return false; 

		// check balance           
		int l_Height;
                    if (node.left == null)
                    //BUG FIX:this is no part of original repOK() from Roops
                    //BUG in repOK: height of null should be -1;
                    //l_Height = -1 ;
                      l_Height = 0 ;
                    else
                      l_Height = node.left.height;

		int r_Height;
                    if (node.right == null)
                    //BUG FIX:this is no part of original repOK() from Roops
                    // BUG in repOK: height of null should be -1;
                    // r_Height = -1 ;
                      r_Height = 0 ;
                    else
                      r_Height = node.right.height;

		int difference = l_Height - r_Height;
		if (difference < -1 || difference > 1)
			return false; // Not balanced.

		int max;
                    if (l_Height > r_Height)
                      max = l_Height ;
                    else
                      max = r_Height;

		if (node.height != 1 + max)
			return false; // Wrong height.

    // visit descendants
		if (node.left != null)
			stack.push(node.left);

		if (node.right != null)
			stack.push(node.right);

	}
	
	if (!repOK_isOrdered(root))
		return false;
	
	
	return true;
}

        private boolean repOK_isOrdered(AvlNode n) {
            if (n==null)
              return true;

            int min = repOK_isOrderedMin(n);
            int max = repOK_isOrderedMax(n);

            return repOK_isOrdered(n, min, max);
        }

        private boolean repOK_isOrdered(AvlNode n, int min, int max) {

            if ((n.element<min ) || (n.element>max))
                return false;

            if (n.left != null) {
                if (!repOK_isOrdered(n.left, min, n.element))
                    return false;
            }
            if (n.right != null) {
                if (!repOK_isOrdered(n.right, n.element, max))
                    return false;
            }
            return true;
        }

        private int repOK_isOrderedMin(AvlNode n) {
          AvlNode curr = n;
          while (curr.left!=null) {
            curr = curr.left;
          }
          return curr.element;
        }

        private int repOK_isOrderedMax(AvlNode n) {
          AvlNode curr = n;
          while (curr.right!=null) {
            curr = curr.right;
          }
          return curr.element;
        }
        
        
        /**************************Finitizaion**************************************/
    	
    	public static IFinitization finAvlTree(int maxSize) {
    		return finAvlTree(maxSize, 0, maxSize -1);
    	}

    	/**To generate AvlTrees that have a given number of nodes, the Korat
      search algorithm uses the finitization method.
      In this method we specify bounds on the number of objects to be used to 
      construct instances of the data structure, as well as possible values 
      stored in the fields of those objects.
    	 */
    	public static IFinitization finAvlTree(int numAvlNode, int minKey, int maxKey) {

    		IFinitization f = FinitizationFactory.create(AvlTree.class);

    		IObjSet entry = f.createObjSet(AvlNode.class,numAvlNode);
    		entry.setNullAllowed(true);
    		IClassDomain entryClassDomain = f.createClassDomain(AvlNode.class);
    		entry.addClassDomain(entryClassDomain);
    		entryClassDomain.includeInIsomorphismCheck(true);


    		IIntSet height = f.createIntSet(minKey, maxKey);

    		IIntSet elems = f.createIntSet(minKey, maxKey);

    		f.set("root", entry);
    		f.set("AvlNode.element", elems);
    		f.set("AvlNode.height", height);        
    		f.set("AvlNode.left", entry);
    		f.set("AvlNode.right", entry);

    		return f;

    	}

}
//$endcategory roops.core.objects

