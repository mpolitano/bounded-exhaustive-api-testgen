package korat.examples.binheap;


import java.util.HashSet;
import java.io.Serializable;

// internal class BinomialHeapNode
    public  class BinomialHeapNode implements Serializable {

        /**
		 * 
		 */
		private static final long serialVersionUID = 1L;

		public int key; // element in current node

        // depth of the binomial tree having the current node as its root
        public int degree;

        // pointer to the parent of the current node
        public BinomialHeapNode parent;

        // pointer to the next binomial tree in the list
        public BinomialHeapNode sibling;

        // pointer to the first child of the current node
        public BinomialHeapNode child;

        public BinomialHeapNode(int k) {
            key = k;
            degree = 0;
            parent = null;
            sibling = null;
            child = null;
        }
        
        public int getSize() {
            return (1 + ((child == null) ? 0 : child.getSize()) + ((sibling == null) ? 0
                    : sibling.getSize()));
        }

        public BinomialHeapNode reverse(BinomialHeapNode sibl) {
            BinomialHeapNode ret;
            if (sibling != null)
                ret = sibling.reverse(this);
            else
                ret = this;
            sibling = sibl;
            return ret;
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

        public String toString() {
            BinomialHeapNode temp = this;
            String ret = "";
            while (temp != null) {
                ret += "(";
                if (temp.parent == null)
                    ret += "Parent: null";
                else
                    ret += "Parent: " + temp.parent.key;
                ret += "  Degree: " + temp.degree + "  Key: " + temp.key + ") ";
                if (temp.child != null)
                    ret += temp.child.toString();
                temp = temp.sibling;
            }
            if (parent == null)
                ret += " ";
            return ret;
        }

        // procedures used by Korat
        private boolean repCheckWithRepetitions(int key_, int degree_,
                Object parent_, HashSet<BinomialHeapNode> nodesSet) {

            BinomialHeapNode temp = this;

            int rightDegree = 0;
            if (parent_ == null) {
                while ((degree_ & 1) == 0) {
                    rightDegree += 1;
                    degree_ /= 2;
                }
                degree_ /= 2;
            } else
                rightDegree = degree_;

            while (temp != null) {
                if ((temp.degree != rightDegree) || (temp.parent != parent_)
                        || (temp.key < key_) || (nodesSet.contains(temp)))
                    return false;
                else {
                    nodesSet.add(temp);
                    if (temp.child == null) {
                        temp = temp.sibling;

                        if (parent_ == null) {
                            if (degree_ == 0)
                                return (temp == null);
                            while ((degree_ & 1) == 0) {
                                rightDegree += 1;
                                degree_ /= 2;
                            }
                            degree_ /= 2;
                            rightDegree++;
                        } else
                            rightDegree--;
                    } else {
                        boolean b = temp.child.repCheckWithRepetitions(
                                temp.key, temp.degree - 1, temp, nodesSet);
                        if (!b)
                            return false;
                        else {
                            temp = temp.sibling;

                            if (parent_ == null) {
                                if (degree_ == 0)
                                    return (temp == null);
                                while ((degree_ & 1) == 0) {
                                    rightDegree += 1;
                                    degree_ /= 2;
                                }
                                degree_ /= 2;
                                rightDegree++;
                            } else
                                rightDegree--;
                        }
                    }
                }
            }

            return true;
        }

        private boolean repCheckWithoutRepetitions(int key_,
                HashSet<Integer> keysSet, int degree_, // equal keys not allowed
                Object parent_, HashSet<BinomialHeapNode> nodesSet) {
            BinomialHeapNode temp = this;

            int rightDegree = 0;
            if (parent_ == null) {
                while ((degree_ & 1) == 0) {
                    rightDegree += 1;
                    degree_ /= 2;
                }
                degree_ /= 2;
            } else
                rightDegree = degree_;

            while (temp != null) {
                if ((temp.degree != rightDegree) || (temp.parent != parent_)
                        || (temp.key <= key_) || (nodesSet.contains(temp))
                        || (keysSet.contains(temp.key))) {
                    return false;
                } else {
                    nodesSet.add(temp);
                    keysSet.add(temp.key);
                    if (temp.child == null) {
                        temp = temp.sibling;

                        if (parent_ == null) {
                            if (degree_ == 0)
                                return (temp == null);
                            while ((degree_ & 1) == 0) {
                                rightDegree += 1;
                                degree_ /= 2;
                            }
                            degree_ /= 2;
                            rightDegree++;
                        } else
                            rightDegree--;
                    } else {
                        boolean b = temp.child.repCheckWithoutRepetitions(
                                temp.key, keysSet, temp.degree - 1, temp,
                                nodesSet);
                        if (!b)
                            return false;
                        else {
                            temp = temp.sibling;

                            if (parent_ == null) {
                                if (degree_ == 0)
                                    return (temp == null);
                                while ((degree_ & 1) == 0) {
                                    rightDegree += 1;
                                    degree_ /= 2;
                                }
                                degree_ /= 2;
                                rightDegree++;
                            } else
                                rightDegree--;
                        }
                    }
                }
            }

            return true;
        }

        public  boolean repOk(int size) {
            // replace 'repCheckWithoutRepetitions' with
            // 'repCheckWithRepetitions' if you don't want to allow equal keys
            return repCheckWithRepetitions(0, size, null,
                    new HashSet<BinomialHeapNode>());
        }

        boolean checkDegree(int degree) {
            for (BinomialHeapNode current = this.child; current != null; current = current.sibling) {
                degree--;
                if (current.degree != degree)
                    return false;
                if (!current.checkDegree(degree))
                    return false;
            }
            return (degree == 0);
        }

        boolean isHeapified() {
            for (BinomialHeapNode current = this.child; current != null; current = current.sibling) {
                if (!(key <= current.key))
                    return false;
                if (!current.isHeapified())
                    return false;
            }
            return true;
        }

        boolean isTree(java.util.Set<NodeWrapper> visited,
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
