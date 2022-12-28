package korat.examples.fibheap;

import java.util.HashSet;
import java.util.Set;

@SuppressWarnings("unused")
public class FibonacciHeapNode implements java.io.Serializable {
    
    private static final long serialVersionUID = 1L;

    protected int key; // the key of the node

    protected int degree; // number of children of the node

    protected FibonacciHeapNode parent; // the parent of the node

    protected FibonacciHeapNode child; // a child of the node

    protected FibonacciHeapNode left; // the node to the left of the current

    // node

    protected FibonacciHeapNode right; // the node to the right of the current

    // node

    protected boolean mark; // a special mark

    /**
     * The reverse of the link operation: removes x from the child
     * list of this node.
     *
     * <p><em>Running time: O(1)</em></p>
     *
     * @param  x    child to be removed from this node's child list
     * @param  min  the minimum heap node, to which x is added.
     */
    public void cut(FibonacciHeapNode x, FibonacciHeapNode min) {
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
     * Two-arg constructor which sets the data and key fields to the
     * passed arguments. It also initializes the right and left pointers,
     * making this a circular doubly-linked list.
     *
     * @param  key   key value for this data object
     */
    public FibonacciHeapNode(int key) {
        this.key = key;
        right = this;
        left = this;
        parent = null;
        child = null;
    }

    public int getSize(FibonacciHeapNode fibNode) {
        int result = 1;
        if (child != null)
            result += child.getSize(child);
        if (right != fibNode)
            result += right.getSize(fibNode);
        return result;
    }

    public boolean contains(FibonacciHeapNode start, FibonacciHeapNode node) {
        FibonacciHeapNode temp = start;
        do {
            if (temp == node)
                return true;
            else
                temp = temp.right;
        } while (temp != start);
        return false;
    }


    private boolean isEqualTo(FibonacciHeapNode node) {
        FibonacciHeapNode tempThis = this;
        FibonacciHeapNode tempThat = node;
        do {
            if ((tempThis.key != tempThat.key)
                    || (tempThis.degree != tempThat.degree)
                    || (tempThis.mark != tempThat.mark)
                    || ((tempThis.child != null) && (tempThat.child == null))
                    || ((tempThis.child == null) && (tempThat.child != null))
                    || ((tempThis.child != null) && (!tempThis.child.isEqualTo(tempThat.child))))
                return false;
            else {
                tempThis = tempThis.right;
                tempThat = tempThat.right;
            }
        } while (tempThis.right != this);
        return true;
    }

    public boolean equals(Object that) {
        if ((!(that instanceof FibonacciHeapNode)) || (that == null))
            return false;
        return isEqualTo((FibonacciHeapNode) that);
    }

    private FibonacciHeapNode findKey(FibonacciHeapNode start, int k) {
        FibonacciHeapNode temp = start;
        do
            if (temp.key == k)
                return temp;
            else {
                FibonacciHeapNode child_temp = null;
                if ((temp.key < k) && (temp.child != null))
                    child_temp = temp.child.findKey(temp.child, k);
                if (child_temp != null)
                    return child_temp;
                else
                    temp = temp.right;
            } while (temp != start);
        return null;
    }

    private boolean numberOfChildrenIsCorrect() {
        if ((child == null) || (degree == 0))
            return ((child == null) && (degree == 0));
        else {
            HashSet<Integer> child_set = new HashSet<Integer>();
            FibonacciHeapNode temp_child = child;
            for (int i = 0; i < degree; i++) {
                // Would crash for some reason... (I got a segmentation fault)
                // if (!child_set.add(temp_child)) return false; // found a
                // loop!
                if (!child_set.add(temp_child.hashCode()))
                    return false; // found a loop!
                temp_child = temp_child.right;
                if (temp_child == null)
                    return false;
            }
            return (temp_child == child);
        }
    }

    // used by Korat
    public boolean repOK(FibonacciHeapNode start, FibonacciHeapNode par, int k,
            HashSet<FibonacciHeapNode> set) {
        if ((!set.add(this)) || (parent != par) || (key < k)
                || (!numberOfChildrenIsCorrect()) || (right == null)
                || (right.left != this) || (left == null)
                || (left.right != this))
            return false;
        boolean b = true;
        if (child != null)
            b = child.repOK(child, this, key, new HashSet<FibonacciHeapNode>());
        if (!b)
            return false;
        if (right == start)
            return true;
        else
            return right.repOK(start, par, k, set);
    }

    int numberOfChildren() {
        if (child == null)
            return 0;
        int num = 1;
        for (FibonacciHeapNode current = child.right; current != child; current = current.right) {
            num++;
        }
        return num;
    }

    boolean checkDegrees() {
        FibonacciHeapNode current = this;
        do {
            if (current.numberOfChildren() != current.degree)
                return false;
            if (current.child != null)
                if (!current.child.checkDegrees())
                    return false;
            current = current.right;
        } while (current != this);
        return true;
    }

    boolean checkHeapified() {
        touch(key);
        if (child == null)
            return true;
        FibonacciHeapNode current = child;
        do {
            if (current.key < key)
                return false;
            if (!current.checkHeapified())
                return false;
            current = current.right;
        } while (current != child);
        return true;
    }

    void touch(int key) {
    }

    boolean isStructural(Set<FibonacciHeapNode> visited,
            FibonacciHeapNode parent) {
        FibonacciHeapNode current = this;
        do {
            if (current.parent != parent)
                return false;
            // if (!visited.add(new IdentityWrapper(current)))
            if (!visited.add(current))
                return false;
            if ((current.child != null)
                    && (!current.child.isStructural(visited, current)))
                return false;
            if (current.right == null)
                return false;
            if (current.right.left != current)
                return false;
            current = current.right;
        } while (current != this);
        return true;
    }
    
    public FibonacciHeapNode() {}




    /**
     * Performs a cascading cut operation. Cuts this from its parent
     * and then does the same for its parent, and so on up the tree.
     *
     * <p><em>Running time: O(log n)</em></p>
     *
     * @param  min  the minimum heap node, to which nodes will be added.
     */
    public void cascadingCut(FibonacciHeapNode min) {
        FibonacciHeapNode z = parent;
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
     * Make this node a child of the given parent node. All linkages
     * are updated, the degree of the parent is incremented, and
     * mark is set to false.
     *
     * @param  parent  the new parent node.
     */
    public void link(FibonacciHeapNode parent) {
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

        for (FibonacciHeapNode x = child.right; x != child; x = x.right)
            result += x.walk(depth+1);
        }

        return result;
    }
}
