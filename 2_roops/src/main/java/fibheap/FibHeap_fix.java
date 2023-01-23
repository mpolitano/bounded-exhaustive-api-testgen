//$category roops.core.objects

/**
  * source: 
  * FibHeap.java
  *from : http://sciris.shu.edu/~borowski/Puzzle/Puzzle.html
  */
//Authors: Marcelo Frias
//$benchmarkclass
/**
 * @Invariant ( all node: FibHeapNode | node in this.min.*(child @+ right) => ( 
 *              ( node !in (node.*right @- node).child.*(child @+ right) ) && 
 *              ( ( node in this.min.*right ) => (node.parent==null && this.min.cost <= node.cost ) ) && 
 *              ( node.right != null ) && 
 *              ( node.right.left == node ) && 
 *              ( node.degree = #(node.child.*right @- null) ) && 
 *              ( all m: FibHeapNode | ( m in node.child.*(child @+ right) => node.cost <= m.cost ) ) && 
 *              ( node.child != null => node.(child.*right).parent==node ) ) 
 *            ) &&
 * 
 *            ( this.n = #(this.min.*(child @+ right) @- null) ) ;
 */
package fibheap;
import java.util.List;
import java.util.Set;

import korat.finitization.*;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

import java.util.HashSet;

import java.util.LinkedList;
public class FibHeap_fix implements java.io.Serializable{
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;


	//$goals 5
	//$benchmark
	/*public void insertNodeTest(FibHeap fibHeap, FibHeapNode toInsert) {
		if (fibHeap!=null && toInsert!=null && toInsert.left==toInsert && toInsert.right==toInsert && toInsert.parent==null &&  toInsert.child==null && fibHeap.repOK()) {
		  FibHeapNode ret_val = fibHeap.insertNode(toInsert);
		}
	}*/

	//$goals 1
	//$benchmark
	/*public void minimumTest(FibHeap fibHeap) {
		if (fibHeap!=null && fibHeap.repOK()) {
		  FibHeapNode ret_val = fibHeap.minimum();
		}
	}*/

	//$goals 25
	//$benchmark
	/*public void removeMinTest(FibHeap fibHeap) {
		if (fibHeap!=null && fibHeap.repOK()) {
		  FibHeapNode ret_val = fibHeap.removeMin();
		}
	}*/

	public FibHeap_fix() {}
	
	private /*@ nullable @*/FibHeapNode min;

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
    	FibHeapNode[] A = new FibHeapNode[45];

        // For each root list node look for others of the same degree.
    	FibHeapNode start = min;
    	FibHeapNode w = min;
        do {
        	FibHeapNode x = w;
            // Because x might be moved, save its sibling now.
        	FibHeapNode nextW = w.right;
            int d = x.degree;
            while (A[d] != null) {
                // Make one of the nodes a child of the other.
            	FibHeapNode y = A[d];
                if (x.key > y.key) {
                	FibHeapNode temp = y;
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
        for (FibHeapNode a : A) {
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
    public void decreaseKey(FibHeapNode x, int k) {
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
    private void decreaseKey(FibHeapNode x, int k, boolean delete) {
        if (!delete && k > x.key) {
            throw new IllegalArgumentException("cannot increase key value");
        }
        x.key = k;
        FibHeapNode y = x.parent;
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
    public void delete(FibHeapNode x) {
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
    	FibHeapNode node = new FibHeapNode(key);
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
    public /*FibHeapNode*/ int min() {
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
    	FibHeapNode z = min;
        //if (z == null) {
          //  return null;
        //}
    	if(z!=null) {
	        if (z.child != null) {
	            z.child.parent = null;
	            // for each child of z do...
	            for (FibHeapNode x = z.child.right; x != z.child; x = x.right) {
	                // set parent[x] to null
	                x.parent = null;
	            }
	            // merge the children into root list
	            FibHeapNode minleft = min.left;
	            FibHeapNode zchildleft = z.child.left;
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
    private static FibHeap_fix union(FibHeap_fix H1, FibHeap_fix H2) {
    	FibHeap_fix H = new FibHeap_fix();
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

	
	
    //*************************************************************************
    //************** From now on repOK()  *************************************
    //*************************************************************************
    //Original from Roops
    public boolean repOK() {
    	Set allNodes = new HashSet();
    	List parent_headers_to_visit = new LinkedList();
        //BUG FIX:this is no part of original repOK() from Roops
        //BUG in repOK:// IF min is null, n must be 0
        if (min ==null) return n==0;

    	if (min != null) {
    	    //System.out.println(min.toString());
    		// check first level 
    		{
    			int child_cound = 0;
    			/* @ nullable */ FibHeapNode curr = new FibHeapNode();
    			curr =  min;
                //System.out.println(curr.toString());

    			do  {
                    //BUG FIX:this is no part of original repOK() from Roops
                    //BUG in repOK:// left and rigth, can't be null. It is a circular list.
                    //We have to fix it for korat to work
    				if(curr.left==null || curr.right ==null)
    					return false;
    				
    				if (n != 0 && curr.left.right != curr)
    					return false;
                    //System.out.println(curr.toString());

                    //BUG FIX:this is no part of original repOK() from Roops
                    //BUG in repOK:// Min node should always contain the minimum value in the heap
                    if (curr.key<min.key)
                     return false;

    				if (curr.parent != null)
    					return false;
    				
    				if (curr.child != null){
    					parent_headers_to_visit.add(curr);
                    }
                    //BUG FIX:this is no part of original repOK() from Roops
                    //BUG in repOK:// If a node has no child its degree should be zero
                else if(curr.degree!=0) return false;   
    				if (!allNodes.add(curr))
    					return false;
    				
    				curr = curr.left;
    				child_cound++;
    			
    			} while (curr!=min);
    			
    		}

    		while (!parent_headers_to_visit.isEmpty()) {

    			// check other levels 

    			FibHeapNode node = (FibHeapNode) parent_headers_to_visit.get(0);
    			parent_headers_to_visit.remove(0);

    			int node_count = 0;
    			FibHeapNode curr_node = node.child;
    			do {
                    //BUG FIX:this is no part of original repOK() from Roops
                    //BUG in repOK:// left and rigth, can't be null. It is a circular list.
                    //We have to fix it for korat to work		
    				if(curr_node.left==null || curr_node.right ==null)
    					return false;
    				
    				if (curr_node.left.right != curr_node)
    					return false;

    				if (curr_node.parent != null)
    					return false;

    				if (curr_node.child != null)
    					parent_headers_to_visit.add(curr_node);

                    //BUG FIX:this is no part of original repOK() from Roops
                    //BUG in repOK:// Child nodes should have smaller keys than their parents
                    if (curr_node.key<node.key)
    				// if (curr_node.key>node.key)
    					return false;
    				
    				if (!allNodes.add(curr_node))
    					return false; // repeated node
    				
    				
    				curr_node = curr_node.left;
    				node_count++;
    				
    			} while (curr_node != node.child);

    			if (node_count != node.degree)
    				return false;

    		}

	}
	
        if (!allNodes.contains(min))
            return false;
    	if (allNodes.size() != this.n)
    		return false;

    	return true;
    }
	
    public String toString()
    {
	String result = "n = " + n + "\n";

	if (min != null) {
	    result += min.walk(0);

	    for (FibHeapNode x = min.right; x!=null && x != min; x = x.right)
	    	result += x.walk(0);
	}

	return result;
    }
	
	//From Korat
    public static IFinitization finFibHeap_fix(int size) {
        IFinitization f = FinitizationFactory.create(FibHeap_fix.class);

        IObjSet heaps = f.createObjSet(FibHeapNode.class, size,true);
        heaps.addClassDomain(f.createClassDomain(FibHeapNode.class,
                size));
        heaps.setNullAllowed(true);

        IFieldDomain sizes = f.createIntSet(0, size);

        f.set("n", sizes);
        //f.set("Nodes", heaps);
        f.set("min", heaps);
        f.set(FibHeapNode.class, "parent", heaps);
        f.set(FibHeapNode.class, "right", heaps);
        f.set(FibHeapNode.class, "left", heaps);
        f.set(FibHeapNode.class, "child", heaps);

        IFieldDomain keys;
        IFieldDomain degrees;
        if (size == 0) {
            keys = f.createIntSet(0, 0);
            degrees = f.createIntSet(0, 0);

        } else {
            keys = f.createIntSet(0, size-1);
            degrees = f.createIntSet(0, size-1);

        }
        f.set(FibHeapNode.class, "key", keys);
        f.set(FibHeapNode.class, "degree", degrees);

        return f;
    }
	
}
//$endcategory roops.core.objects
