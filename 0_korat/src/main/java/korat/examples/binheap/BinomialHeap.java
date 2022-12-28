package korat.examples.binheap;

import java.io.Serializable;
import java.util.HashSet;

import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;


@SuppressWarnings("unused")
public class BinomialHeap  implements Serializable {

    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	

   

    // end of helper class BinomialHeapNode

    private BinomialHeapNode Nodes;

    private int size;

    /*
     * Builders ---------------------------
     */
    
	public BinomialHeap() {
		Nodes = null;
		size = 0;
	}
	
	// 2. Find the minimum key
	/**
	 * @Modifies_Everything
	 * 
	 * @Requires some this.nodes ;
	 * @Ensures ( some x: BinomialHeapNode | x in this.nodes && x.key == return
	 *          ) && ( all y : BinomialHeapNode | ( y in this.nodes && y!=return
	 *          ) => return <= y.key ) ;
	 */
	public int findMinimum() {
		return Nodes.findMinNode().key;
	}

	// 3. Unite two binomial heaps
	// helper procedure
	private void merge(/* @ nullable @ */BinomialHeapNode binHeap) {
		BinomialHeapNode temp1 = Nodes, temp2 = binHeap;
		while ((temp1 != null) && (temp2 != null)) {
			if (temp1.degree == temp2.degree) {
				BinomialHeapNode tmp = temp2;
				temp2 = temp2.sibling;
				tmp.sibling = temp1.sibling;
				temp1.sibling = tmp;
				temp1 = tmp.sibling;
			} else {
				if (temp1.degree < temp2.degree) {
					if ((temp1.sibling == null) || (temp1.sibling.degree > temp2.degree)) {
						BinomialHeapNode tmp = temp2;
						temp2 = temp2.sibling;
						tmp.sibling = temp1.sibling;
						temp1.sibling = tmp;
						temp1 = tmp.sibling;
					} else {
						temp1 = temp1.sibling;
					}
				} else {
					BinomialHeapNode tmp = temp1;
					temp1 = temp2;
					temp2 = temp2.sibling;
					temp1.sibling = tmp;
					if (tmp == Nodes) {
						Nodes = temp1;
					}
				}
			}
		}

		if (temp1 == null) {
			temp1 = Nodes;
			while (temp1.sibling != null) {
				temp1 = temp1.sibling;
			}
			temp1.sibling = temp2;
		}

	}

	// another helper procedure
	private void unionNodes(/* @ nullable @ */BinomialHeapNode binHeap) {
		merge(binHeap);

		BinomialHeapNode prevTemp = null, temp = Nodes, nextTemp = Nodes.sibling;

		while (nextTemp != null) {
			if ((temp.degree != nextTemp.degree) || ((nextTemp.sibling != null) && (nextTemp.sibling.degree == temp.degree))) {
				prevTemp = temp;
				temp = nextTemp;
			} else {
				if (temp.key <= nextTemp.key) {
					temp.sibling = nextTemp.sibling;
					nextTemp.parent = temp;
					nextTemp.sibling = temp.child;
					temp.child = nextTemp;
					temp.degree++;
				} else {
					if (prevTemp == null) {
						Nodes = nextTemp;
					} else {
						prevTemp.sibling = nextTemp;
					}
					temp.parent = nextTemp;
					temp.sibling = nextTemp.child;
					nextTemp.child = temp;
					nextTemp.degree++;
					temp = nextTemp;
				}
			}

			nextTemp = temp.sibling;
		}
	}

	// 4. Insert a node with a specific value
	/**
	 * @Modifies_Everything
	 * 
	 * @Ensures some n: BinomialHeapNode | ( n !in @old(this.nodes) &&
	 *          this.nodes = @old(this.nodes) @+ n && n.key = value ) ;
	 */
	public void insert(int value) {
			BinomialHeapNode temp = new BinomialHeapNode(value);
			if (Nodes == null) {
				Nodes = temp;
				size = 1;
			} else {
				unionNodes(temp);
				size++;
			}
	}

	// 5. Extract the node with the minimum key
	/**
	 * @Modifies_Everything
	 * 
	 * @Ensures ( @old(this).@old(Nodes)==null => ( this.Nodes==null && return==null ) ) 
	 *       && ( @old(this).@old(Nodes)!=null => ( 
	 *               (return in @old(this.nodes)) && 
	 *               ( all y : BinomialHeapNode | ( y in @old(this.nodes.key) && y.key >= return.key ) ) && 
	 *               (this.nodes=@old(this.nodes) @- return ) && 
	 *               (this.nodes.key @+ return.key = @old(this.nodes.key) ) ));
	 */
	public/* @ nullable @ *//*BinomialHeapNode*/ int extractMin() {
		//if (Nodes == null)
		//	return null;

		BinomialHeapNode temp = Nodes, prevTemp = null;
		BinomialHeapNode minNode = null;

		minNode = Nodes.findMinNode();
		while (temp.key != minNode.key) {
			prevTemp = temp;
			temp = temp.sibling;
		}

		if (prevTemp == null) {
			Nodes = temp.sibling;
		} else {
			prevTemp.sibling = temp.sibling;
		}
		temp = temp.child;
		BinomialHeapNode fakeNode = temp;
		while (temp != null) {
			temp.parent = null;
			temp = temp.sibling;
		}

		if ((Nodes == null) && (fakeNode == null)) {
			size = 0;
		} else {
			if ((Nodes == null) && (fakeNode != null)) {
				Nodes = fakeNode.reverse(null);
				size--;
			} else {
				if ((Nodes != null) && (fakeNode == null)) {
					size--;
				} else {
					unionNodes(fakeNode.reverse(null));
					size--;
				}
			}
		}

		return minNode.key;
	}

	// 6. Decrease a key value
	private void decreaseKeyValue(int old_value, int new_value) {
		BinomialHeapNode temp = Nodes.findANodeWithKey(old_value);
		decreaseKeyNode(temp, new_value);
	}

	/**
	 * 
	 * @Modifies_Everything
	 * 
	 * @Requires node in this.nodes && node.key >= new_value ;
	 * 
	 * @Ensures (some other: BinomialHeapNode | other in this.nodes &&
	 *          other!=node && @old(other.key)=@old(node.key)) ? this.nodes.key
	 *          = @old(this.nodes.key) @+ new_value : this.nodes.key =
	 * @old(this.nodes.key) @- @old(node.key) @+ new_value ;
	 */
	public void decreaseKeyNode(final BinomialHeapNode node, final int new_value) {
		if (node == null)
			return;

		BinomialHeapNode y = node;
		y.key = new_value;
		BinomialHeapNode z = node.parent;

		while ((z != null) && (node.key < z.key)) {
			int z_key = y.key;
			y.key = z.key;
			z.key = z_key;

			y = z;
			z = z.parent;
		}
	}

	// 7. Delete a node with a certain key
	public void delete(int value) {
		if ((Nodes != null) && (Nodes.findANodeWithKey(value) != null)) {
			decreaseKeyValue(value, findMinimum() - 1);
			extractMin();
		}
	}
    

    public String toString() {
        if (Nodes == null)
            return size + "\n()\n";
        else
            return size + "\n" + Nodes.toString();
    }

    // procedures used by Korat
    public boolean repOkOld() {
        if (size == 0)
            return (Nodes == null);
        if (Nodes == null)
            return false;

        return (Nodes.repOk(size)) && (size == Nodes.getSize());
    }

    boolean checkDegrees() {
        int degree_ = size;
        int rightDegree = 0;
        for (BinomialHeapNode current = Nodes; current != null; current = current.sibling) {
            if (degree_ == 0)
                return false;
            while ((degree_ & 1) == 0) {
                rightDegree++;
                degree_ /= 2;
            }
            if (current.degree != rightDegree)
                return false;
            if (!current.checkDegree(rightDegree))
                return false;
            rightDegree++;
            degree_ /= 2;
        }
        return (degree_ == 0);
    }

    boolean checkHeapified() {
        for (BinomialHeapNode current = Nodes; current != null; current = current.sibling) {
            if (!current.isHeapified())
                return false;
        }
        return true;
    }

    public boolean repOK() {
        if (size == 0)
            return (Nodes == null);
        if (Nodes == null)
            return false;
        // checks that list of trees has no cycles
        java.util.Set<NodeWrapper> visited = new java.util.HashSet<NodeWrapper>();
        for (BinomialHeapNode current = Nodes; current != null; current = current.sibling) {
            // checks that the list has no cycle
            if (!visited.add(new NodeWrapper(current)))
                return false;
            if (!current.isTree(visited, null))
                return false;
        }
        // checks that the total size is consistent
        if (visited.size() != size)
            return false;
        // checks that the degrees of all trees are binomial
        if (!checkDegrees())
            return false;
        // checks that keys are heapified
        if (!checkHeapified())
            return false;
        return true;
    }
    
    public static IFinitization finBinomialHeap(int size) {

        IFinitization f = FinitizationFactory.create(BinomialHeap.class);

        IClassDomain heapsDomain = f.createClassDomain(BinomialHeapNode.class,
                size);
        IObjSet heaps = f.createObjSet(BinomialHeapNode.class);
        heaps.setNullAllowed(true);
        heaps.addClassDomain(heapsDomain);

        f.set("size", f.createIntSet(0, size));
        f.set("Nodes", heaps);
        f.set(BinomialHeapNode.class, "parent", heaps);
        f.set(BinomialHeapNode.class, "sibling", heaps);
        f.set(BinomialHeapNode.class, "child", heaps);
        f.set(BinomialHeapNode.class, "key", f.createIntSet(0, size -1));
        f.set(BinomialHeapNode.class, "degree", f.createIntSet(0, size));

        return f;
    }

}
