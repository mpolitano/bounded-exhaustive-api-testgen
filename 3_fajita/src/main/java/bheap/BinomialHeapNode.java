/**
 * 
 */
package bheap;


public class BinomialHeapNode implements java.io.Serializable{

	/**
	 * 
	 */
	private static final long serialVersionUID = 4343741789027176035L;

	int key; // element in current node

	int degree; // depth of the binomial tree having the current node as its root

	/*@ nullable @*/BinomialHeapNode parent; // pointer to the parent of the current node

	/*@ nullable @*/BinomialHeapNode sibling; // pointer to the next binomial tree in the list

	/*@ nullable @*/BinomialHeapNode child; // pointer to the first child of the current node

	public BinomialHeapNode(int k) {
		//	public BinomialHeapNode(Integer k) {
		key = k;
		degree = 0;
		parent = null;
		sibling = null;
		child = null;
	}

	public int getKey() { // returns the element in the current node
		return key;
	}

	private void setKey(int value) { // sets the element in the current node
		key = value;
	}

	public int getDegree() { // returns the degree of the current node
		return degree;
	}

	private void setDegree(int deg) { // sets the degree of the current node
		degree = deg;
	}

	public BinomialHeapNode getParent() { // returns the father of the current node
		return parent;
	}

	private void setParent(BinomialHeapNode par) { // sets the father of the current node
		parent = par;
	}

	public BinomialHeapNode getSibling() { // returns the next binomial tree in the list
		return sibling;
	}

	private void setSibling(BinomialHeapNode nextBr) { // sets the next binomial tree in the list
		sibling = nextBr;
	}

	public BinomialHeapNode getChild() { // returns the first child of the current node
		return child;
	}

	private void setChild(BinomialHeapNode firstCh) { // sets the first child of the current node
		child = firstCh;
	}

	public int getSize() {
		return (1 + ((child == null) ? 0 : child.getSize()) + ((sibling == null) ? 0
				: sibling.getSize()));
	}


	BinomialHeapNode findMinNode() {
		BinomialHeapNode x = this, y = this;
		int min = x.key;

		while (x != null) {
			if (x.key < min) {
				y = x;
				min = x.key;
			}
			x = x.sibling;
		}

		return y;
	}

	// Find a node with the given key
	BinomialHeapNode findANodeWithKey(int value) {
		BinomialHeapNode temp = this, node = null;
		while (temp != null) {
			if (temp.key == value) {
				node = temp;
				return node;
			}
			if (temp.child == null)
				temp = temp.sibling;
			else {
				node = temp.child.findANodeWithKey(value);
				if (node == null)
					temp = temp.sibling;
				else
					return node;
			}
		}

		return node;
	}
	
    /* Function reverse */
    public BinomialHeapNode reverse(BinomialHeapNode sibl) 
    {
            BinomialHeapNode ret;
            if (sibling != null)
                ret = sibling.reverse(this);
            else
                ret = this;
            sibling = sibl;
            return ret;
    }
	
	public boolean checkDegree(int degree) {
		for (BinomialHeapNode current = this.child; current != null; current = current.sibling) {
			degree--;
			if (current.degree != degree)
				return false;
			if (!current.checkDegree(degree))
				return false;
		}
		return (degree == 0);
	}

	public boolean isHeapified() {
		for (BinomialHeapNode current = this.child; current != null; current = current.sibling) {
			if (!(key <= current.key))
				return false;
			if (!current.isHeapified())
				return false;
		}
		return true;
	}

	public boolean isTree(java.util.Set<NodeWrapper> visited,
			BinomialHeapNode parent) {
		if (this.parent != parent)
			return false;
		for (BinomialHeapNode current = this.child; current != null; current = current.sibling) {
			if (!visited.add(new NodeWrapper(current)))
				return false;
			if (!current.isTree(visited, this))
				return false;
		}
		return true;
	}


	
}