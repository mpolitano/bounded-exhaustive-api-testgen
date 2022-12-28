package korat.examples.fibheap;

import java.util.HashSet;
import java.util.Set;

import korat.finitization.IFieldDomain;
import korat.finitization.IFinitization;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

public class FibonacciHeap  implements java.io.Serializable {
    
    private static final long serialVersionUID = 1L;

    private /*@ nullable @*/FibonacciHeapNode min;

    private int n;
    
    /**
     * Removes all elements from this heap.
     *
     * <p><em>Running time: O(1)</em></p>
     */
    public void clear() {
        min = null;
        n = 0;
    }

    /**
     * Consolidates the trees in the heap by joining trees of equal
     * degree until there are no more trees of equal degree in the
     * root list.
     *
     * <p><em>Running time: O(log n) amortized</em></p>
     */
    private void consolidate() {
        // The magic 45 comes from log base phi of Integer.MAX_VALUE,
        // which is the most elements we will ever hold, and log base
        // phi represents the largest degree of any root list node.
        FibonacciHeapNode[] A = new FibonacciHeapNode[45];

        // For each root list node look for others of the same degree.
        FibonacciHeapNode start = min;
        FibonacciHeapNode w = min;
        do {
            FibonacciHeapNode x = w;
            // Because x might be moved, save its sibling now.
            FibonacciHeapNode nextW = w.right;
            int d = x.degree;
            while (A[d] != null) {
                // Make one of the nodes a child of the other.
                FibonacciHeapNode y = A[d];
                if (x.key > y.key) {
                    FibonacciHeapNode temp = y;
                    y = x;
                    x = temp;
                }
                if (y == start) {
                    // Because removeMin() arbitrarily assigned the min
                    // reference, we have to ensure we do not miss the
                    // end of the root node list.
                    start = start.right;
                }
                if (y == nextW) {
                    // If we wrapped around we need to check for this case.
                    nextW = nextW.right;
                }
                // Node y disappears from root list.
                y.link(x);
                // We've handled this degree, go to next one.
                A[d] = null;
                d++;
            }
            // Save this node for later when we might encounter another
            // of the same degree.
            A[d] = x;
            // Move forward through list.
            w = nextW;
        } while (w != start);

        // The node considered to be min may have been changed above.
        min = start;
        // Find the minimum key again.
        for (FibonacciHeapNode a : A) {
            if (a != null && a.key < min.key) {
                min = a;
            }
        }
    }

    /**
     * Decreases the key value for a heap node, given the new value
     * to take on. The structure of the heap may be changed, but will
     * not be consolidated.
     *
     * <p><em>Running time: O(1) amortized</em></p>
     *
     * @param  x  node to decrease the key of
     * @param  k  new key value for node x
     * @exception  IllegalArgumentException
     *             if k is larger than x.key value.
     */
    public void decreaseKey(FibonacciHeapNode x, int k) {
        decreaseKey(x, k, false);
    }

    /**
     * Decrease the key value of a node, or simply bubble it up to the
     * top of the heap in preparation for a delete operation.
     *
     * @param  x       node to decrease the key of.
     * @param  k       new key value for node x.
     * @param  delete  true if deleting node (in which case, k is ignored).
     */
    private void decreaseKey(FibonacciHeapNode x, int k, boolean delete) {
        if (!delete && k > x.key) {
            throw new IllegalArgumentException("cannot increase key value");
        }
        x.key = k;
        FibonacciHeapNode y = x.parent;
        if (y != null && (delete || k < y.key)) {
            y.cut(x, min);
            y.cascadingCut(min);
        }
        if (delete || k < min.key) {
            min = x;
        }
    }

    /**
     * Deletes a node from the heap given the reference to the node.
     * The trees in the heap will be consolidated, if necessary.
     *
     * <p><em>Running time: O(log n) amortized</em></p>
     *
     * @param  x  node to remove from heap.
     */
    public void delete(FibonacciHeapNode x) {
        // make x as small as possible
        decreaseKey(x, 0, true);
        // remove the smallest, which decreases n also
        removeMin();
    }

    /**
     * Tests if the Fibonacci heap is empty or not. Returns true if
     * the heap is empty, false otherwise.
     *
     * <p><em>Running time: O(1)</em></p>
     *
     * @return  true if the heap is empty, false otherwise.
     */
    public boolean isEmpty() {
        return min == null;
    }

    /**
     * Inserts a new data element into the heap. No heap consolidation
     * is performed at this time, the new node is simply inserted into
     * the root list of this heap.
     *
     * <p><em>Running time: O(1)</em></p>
     *
     * @param  key  key value associated with data object.
     * @return newly created heap node.
     */
    public /*FibHeapNode*/ void insert(int key) {
        FibonacciHeapNode node = new FibonacciHeapNode(key);
        // concatenate node into min list
        if (min != null) {
            node.right = min;
            node.left = min.left;
            min.left = node;
            node.left.right = node;
            if (key < min.key) {
                min = node;
            }
        } else {
            min = node;
        }
        n++;
       // return node;
    }

    /**
     * Returns the smallest element in the heap. This smallest element
     * is the one with the minimum key value.
     *
     * <p><em>Running time: O(1)</em></p>
     *
     * @return  heap node with the smallest key, or null if empty.
     */
    public int min() {
        return min.key;
    }

    /**
     * Removes the smallest element from the heap. This will cause
     * the trees in the heap to be consolidated, if necessary.
     *
     * <p><em>Running time: O(log n) amortized</em></p>
     *
     * @return  data object with the smallest key.
     */
    public /*FibHeapNode*/ void removeMin() {
        FibonacciHeapNode z = min;
        //if (z == null) {
          //  return null;
        //}
        if(z!=null) {
            if (z.child != null) {
                z.child.parent = null;
                // for each child of z do...
                for (FibonacciHeapNode x = z.child.right; x != z.child; x = x.right) {
                    // set parent[x] to null
                    x.parent = null;
                }
                // merge the children into root list
                FibonacciHeapNode minleft = min.left;
                FibonacciHeapNode zchildleft = z.child.left;
                min.left = zchildleft;
                zchildleft.right = min;
                z.child.left = minleft;
                minleft.right = z.child;
            }
            // remove z from root list of heap
            z.left.right = z.right;
            z.right.left = z.left;
            if (z == z.right) {
                min = null;
            } else {
                min = z.right;
                consolidate();
            }
            // decrement size of heap
            n--;
        }
        //return z;
    }

    /**
     * Returns the size of the heap which is measured in the
     * number of elements contained in the heap.
     *
     * <p><em>Running time: O(1)</em></p>
     *
     * @return  number of elements in the heap.
     */
    public int size() {
        return n;
    }

    /**
     * Joins two Fibonacci heaps into a new one. No heap consolidation is
     * performed at this time. The two root lists are simply joined together.
     *
     * <p><em>Running time: O(1)</em></p>
     *
     * @param  H1  first heap
     * @param  H2  second heap
     * @return  new heap containing H1 and H2
     */
    private static FibonacciHeap union(FibonacciHeap H1, FibonacciHeap H2) {
        FibonacciHeap H = new FibonacciHeap();
        if (H1 != null && H2 != null) {
            H.min = H1.min;
            if (H.min != null) {
                if (H2.min != null) {
                    H.min.right.left = H2.min.left;
                    H2.min.left.right = H.min.right;
                    H.min.right = H2.min;
                    H2.min.left = H.min;
                    if (H2.min.key < H1.min.key) {
                        H.min = H2.min;
                    }
                }
            } else {
                H.min = H2.min;
            }
            H.n = H1.n + H2.n;
        }
        return H;
    }

    
    

    // used by Korat

//    public boolean repOkOld() {
//        if ((Nodes == null) || (Nodes == null))
//            return ((Nodes == null) && (Nodes == null) && (size == 0));
//        else
//            return (Nodes.repOK(Nodes, null, 1,
//                    new HashSet<FibonacciHeapNode>())
//                    && (Nodes.contains(Nodes, Nodes))
//                    && (size == Nodes.getSize(Nodes))
//                    && (getMin() == Nodes.key) && (Nodes.parent == null));
//    }

    public boolean checkHeapified() {
        FibonacciHeapNode current = min;
        do {
            if (!current.checkHeapified())
                return false;
            current = current.right;
        } while (current != min);
        return true;
    }

    public boolean repOK() {
        if ((min == null) )
            return ((min == null) && (n == 0));
        // checks that structural constrainst are satisfied
        Set<FibonacciHeapNode> visited = new HashSet<FibonacciHeapNode>();
        if (!min.isStructural(visited, null))
            return false;
//        if (!Nodes.contains(Nodes, minNode))
//            return false;
        // checks that the total size is consistent
        if (visited.size() != n)
            return false;
        // checks that the degrees of all trees are fibonacci
        if (!min.checkDegrees())
            return false;
        // checks that keys are heapified
        if (!checkHeapified())
            return false;
        if (getMin() != min.key)
            return false;
        return true;
    }


    private int getMin() {
        FibonacciHeapNode temp = min;
        int m = min.key;
        do {
            if (temp.key < m)
                m = temp.key;
            temp = temp.right;
        } while (temp != min);
        return m;
    }

    public static IFinitization finFibonacciHeap(int size) {
        IFinitization f = FinitizationFactory.create(FibonacciHeap.class);

        IObjSet heaps = f.createObjSet(FibonacciHeapNode.class, true);
        heaps.addClassDomain(f.createClassDomain(FibonacciHeapNode.class,
                size));

        IFieldDomain sizes = f.createIntSet(0, size);

        f.set("n", sizes);
        f.set("min", heaps);
        f.set(FibonacciHeapNode.class, "parent", heaps);
        f.set(FibonacciHeapNode.class, "right", heaps);
        f.set(FibonacciHeapNode.class, "left", heaps);
        f.set(FibonacciHeapNode.class, "child", heaps);

        IFieldDomain keys;
        IFieldDomain degrees;
        if (size == 0) {
            keys = f.createIntSet(0, 0);
            degrees = f.createIntSet(0, 0);
        } else {
            keys = f.createIntSet(0, size - 1);
            degrees = f.createIntSet(0, size - 1);
        }
        f.set(FibonacciHeapNode.class, "key", keys);
        f.set(FibonacciHeapNode.class, "degree", degrees);

        return f;
    }

}