//$category roops.core.objects

//Authors: Marcelo Frias
package fibheap;

public class FibHeapNode implements java.io.Serializable{
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;


	public boolean mark = false;
	public int /*cost*/key = 0;
	public int degree = 0;

	public /*@ nullable @*/ FibHeapNode parent;
	public /*@ nullable @*/ FibHeapNode left;
	public /*@ nullable @*/ FibHeapNode right;
	public /*@ nullable @*/ FibHeapNode child;

	public FibHeapNode() {}


	/**
     * Two-arg constructor which sets the data and key fields to the
     * passed arguments. It also initializes the right and left pointers,
     * making this a circular doubly-linked list.
     *
     * @param  key   key value for this data object
     */
    public FibHeapNode(int key) {
        this.key = key;
        right = this;
        left = this;
    }

    /**
     * Performs a cascading cut operation. Cuts this from its parent
     * and then does the same for its parent, and so on up the tree.
     *
     * <p><em>Running time: O(log n)</em></p>
     *
     * @param  min  the minimum heap node, to which nodes will be added.
     */
    public void cascadingCut(FibHeapNode min) {
    	FibHeapNode z = parent;
        // if there's a parent...
        if (z != null) {
            if (mark) {
                // it's marked, cut it from parent
                z.cut(this, min);
                // cut its parent as well
                z.cascadingCut(min);
            } else {
                // if y is unmarked, set it marked
                mark = true;
            }
        }
    }

    /**
     * The reverse of the link operation: removes x from the child
     * list of this node.
     *
     * <p><em>Running time: O(1)</em></p>
     *
     * @param  x    child to be removed from this node's child list
     * @param  min  the minimum heap node, to which x is added.
     */
    public void cut(FibHeapNode x, FibHeapNode min) {
        // remove x from childlist and decrement degree
        x.left.right = x.right;
        x.right.left = x.left;
        degree--;
        // reset child if necessary
        if (degree == 0) {
            child = null;
        } else if (child == x) {
            child = x.right;
        }
        // add x to root list of heap
        x.right = min;
        x.left = min.left;
        min.left = x;
        x.left.right = x;
        // set parent[x] to nil
        x.parent = null;
        // set mark[x] to false
        x.mark = false;
    }

    /**
     * Make this node a child of the given parent node. All linkages
     * are updated, the degree of the parent is incremented, and
     * mark is set to false.
     *
     * @param  parent  the new parent node.
     */
    public void link(FibHeapNode parent) {
        // Note: putting this code here in Node makes it 7x faster
        // because it doesn't have to use generated accessor methods,
        // which add a lot of time when called millions of times.
        // remove this from its circular list
        left.right = right;
        right.left = left;
        // make this a child of x
        this.parent = parent;
        if (parent.child == null) {
            parent.child = this;
            right = this;
            left = this;
        } else {
            left = parent.child;
            right = parent.child.right;
            parent.child.right = this;
            right.left = this;
        }
        // increase degree[x]
        parent.degree++;
        // set mark false
        mark = false;
    }
	
	
    
    
	/** Returns the <code>String</code> representation of this
	 * node's object, along with its degree and mark. */
	public String toString()
	{
	    return "key = " + key +
		", degree = " + degree + ", mark = " + mark;
	}

	/**
	 * Returns the <code>String</code> representation of the
	 * subtree rooted at this node, based on the objects in the
	 * nodes.  It represents the depth of each node by two spaces
	 * per depth preceding the <code>String</code> representation
	 * of the node.
	 *
	 * @param depth Depth of this node.
	 */
	public String walk(int depth)
	{
	    String result = "";

	    for (int i = 0; i < depth; i++)
		result += "  ";

	    result += toString() + "\n";

	    if (child != null) {
		result += child.walk(depth+1);

		for (FibHeapNode x = child.right; x != child; x = x.right)
		    result += x.walk(depth+1);
	    }

	    return result;
	}
	

}
//$endcategory roops.core.objects
