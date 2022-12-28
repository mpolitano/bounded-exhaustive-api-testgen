package korat.examples.redblacktree;

import java.io.Serializable;
import java.util.Set;

import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

@SuppressWarnings("unchecked")
public class RedBlackTree implements Serializable {

    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private Node root = null;

    private int size = 0;

    private static final int RED = 0;

    private static final int BLACK = 1;
 

   public static class Node  {

        int key;

        int value;

        Node left = null;

        Node right = null;

        Node parent;

        int color = BLACK;

    }
    /*
     * Builders ---------------------------
     */
	public boolean contains(int aKey) {
		return getEntry(aKey) != null;
	}

	private Node getEntry(int key) {
		Node p = root;
		while (p != null) {

			if (key == p.key) {
				return p;
			} else if (key < p.key) {
				p = p.left;
			} else {
				p = p.right;
			}
		}
		return null;
	}


	private Node getEntry_remove(int key) {
		Node p = root;
		while (p != null) {

			if (key == p.key) {

				return p;
			} else if (key < p.key) {

				p = p.left;
			} else {

				p = p.right;
			}
		}
		return null;
	}


	private void init_Node(Node entry, int new_key, Node new_parent) {
		entry.color = BLACK;
		entry.left = null;
		entry.right = null;
		entry.key = new_key;
		entry.parent = new_parent;
	}


	public boolean add(int aKey) {
		Node t = root;

		if (t == null) {
			incrementSize();
			root = new Node();
			init_Node(root, aKey, null);

			return false;
		}

		boolean boolean_true= true;
		while (boolean_true) {

			if (aKey == t.key) {

				return true;
			} else if (aKey < t.key) {

				if (t.left != null) {

					t = t.left;
				} else {

					incrementSize();
					t.left = new Node();
					init_Node(t.left, aKey, t);

					fixAfterInsertion(t.left);

					return false;
				}
			} else { // cmp > 0


				if (t.right != null) {
					t = t.right;
				} else {
					incrementSize();
					t.right = new Node();
					init_Node(t.right, aKey, t);
					fixAfterInsertion(t.right);
					return false;
				}
			}
		}
		return false;
	}

	private void incrementSize() {
		size++;
	}


	/**
	 * Balancing operations.
	 *
	 * Implementations of rebalancings during insertion and deletion are
	 * slightly different than the CLR version.  Rather than using dummy
	 * nilnodes, we use a set of accessors that deal properly with null.  They
	 * are used to avoid messiness surrounding nullness checks in the main
	 * algorithms.
	 */

	private static /*boolean*/ int colorOf(Node p) {
		//boolean black = true;
		/*boolean*/int  result ;
		if (p==null)
			//result =black;
			result =BLACK;
		else
			result =p.color;
		return result;
	}

	private static Node parentOf(Node p) {
		Node result;
		if (p == null)
			result = null;
		else
			result = p.parent;

		return result;
	}

	private static void setColor(Node p, /*boolean*/ int c) {
		if (p != null)
			p.color = c;
	}

	private static Node leftOf(Node p) {
		Node result ;
		if (p == null)
			result = null;
		else
			result = p.left;
		return result;
	}

	private static Node rightOf(Node p) {
		Node result;
		if (p == null) 
			result = null;
		else
			result = p.right;
		return result;
	}

	/** From CLR **/
	private void rotateLeft(Node p) {
		Node r = p.right;
		p.right = r.left;
		if (r.left != null)
			r.left.parent = p;
		r.parent = p.parent;
		if (p.parent == null)
			root = r;
		else if (p.parent.left == p)
			p.parent.left = r;
		else
			p.parent.right = r;
		r.left = p;
		p.parent = r;
	}

	/** From CLR **/
	private void rotateRight(Node p) {
		Node l = p.left;
		p.left = l.right;
		if (l.right != null)
			l.right.parent = p;
		l.parent = p.parent;
		if (p.parent == null)
			root = l;
		else if (p.parent.right == p)
			p.parent.right = l;
		else
			p.parent.left = l;
		l.right = p;
		p.parent = l;
	}

	/** From CLR **/
	private void fixAfterInsertion(final Node entry) {
		Node x = entry;
		x.color = RED;

		while (x != null && x != root && x.parent.color == RED) {

			if (parentOf(x) == leftOf(parentOf(parentOf(x)))) {
				Node y = rightOf(parentOf(parentOf(x)));
				if (colorOf(y) == RED) {
					setColor(parentOf(x), BLACK);
					setColor(y, BLACK);
					setColor(parentOf(parentOf(x)), RED);
					x = parentOf(parentOf(x));
				} else {
					if (x == rightOf(parentOf(x))) {
						x = parentOf(x);
						rotateLeft(x);
					} else {
					}
					setColor(parentOf(x), BLACK);
					setColor(parentOf(parentOf(x)), RED);
					if (parentOf(parentOf(x)) != null) {
						rotateRight(parentOf(parentOf(x)));
					} else {
					}
				}
			} else {
				Node y = leftOf(parentOf(parentOf(x)));
				if (colorOf(y) == RED) {
					setColor(parentOf(x), BLACK);
					setColor(y, BLACK);
					setColor(parentOf(parentOf(x)), RED);
					x = parentOf(parentOf(x));
				} else {
					if (x == leftOf(parentOf(x))) {
						x = parentOf(x);
						rotateRight(x);
					} else {
					}
					setColor(parentOf(x), BLACK);
					setColor(parentOf(parentOf(x)), RED);
					if (parentOf(parentOf(x)) != null) {
						rotateLeft(parentOf(parentOf(x)));
					} else {
					}

				}
			}
		}
		root.color = BLACK;
	}




	public boolean remove(int aKey) {
		Node p = getEntry_remove(aKey);
		if (p == null) {
			return false;
		}


		deleteEntry(p);

		return true;
	}

	/**
	 * Delete node p, and then rebalance the tree.
	 */
	private void deleteEntry(Node p) {
		decrementSize();

		// If strictly internal, copy successor's element to p and then make p
		// point to successor.
		if (p.left != null && p.right != null) {
			Node s = successor(p);
			p.key = s.key;

			p = s;
		} // p has 2 children

		// Start fixup at replacement node, if it exists.
		Node replacement;
		if (p.left != null )
			replacement = p.left ;
		else
			replacement = p.right;

		if (replacement != null) {

			// Link replacement to parent
			replacement.parent = p.parent;
			if (p.parent == null) {
				root = replacement;
			} else if (p == p.parent.left){
				p.parent.left = replacement;
			} else {
				p.parent.right = replacement;
			}

			// Null out links so they are OK to use by fixAfterDeletion.
			p.left = p.right = p.parent = null;

			// Fix replacement
			if (p.color == BLACK) {
				fixAfterDeletion(replacement);
			}
		} else if (p.parent == null) { // return if we are the only node.
			root = null;
		} else { //  No children. Use self as phantom replacement and unlink.
			if (p.color == BLACK) {
				fixAfterDeletion(p);
			}

			if (p.parent != null) {
				if (p == p.parent.left) {
					p.parent.left = null;
				} else if (p == p.parent.right) {
					p.parent.right = null;
				}
				p.parent = null;
			}
		}
	}

	/** From CLR **/
	private void fixAfterDeletion(final Node entry) {
		Node x = entry;

		while (x != root && colorOf(x) == BLACK) {

			if (x == leftOf(parentOf(x))) {
				Node sib = rightOf(parentOf(x));

				if (colorOf(sib) == RED) {
					setColor(sib, BLACK);
					setColor(parentOf(x), RED);
					rotateLeft(parentOf(x));
					sib = rightOf(parentOf(x));
				}

				if (colorOf(leftOf(sib)) == BLACK
						&& colorOf(rightOf(sib)) == BLACK) {

					setColor(sib, RED);
					x = parentOf(x);
				} else {
					if (colorOf(rightOf(sib)) == BLACK) {
						setColor(leftOf(sib), BLACK);
						setColor(sib, RED);
						rotateRight(sib);
						sib = rightOf(parentOf(x));
					}
					setColor(sib, colorOf(parentOf(x)));
					setColor(parentOf(x), BLACK);
					setColor(rightOf(sib), BLACK);
					rotateLeft(parentOf(x));
					x = root;
				}
			} else { // symmetric
				Node sib = leftOf(parentOf(x));

				if (colorOf(sib) == RED) {
					setColor(sib, BLACK);
					setColor(parentOf(x), RED);
					rotateRight(parentOf(x));
					sib = leftOf(parentOf(x));
				}

				if (colorOf(rightOf(sib)) == BLACK
						&& colorOf(leftOf(sib)) == BLACK) {
					setColor(sib, RED);
					x = parentOf(x);
				} else {
					if (colorOf(leftOf(sib)) == BLACK) {
						setColor(rightOf(sib), BLACK);
						setColor(sib, RED);
						rotateLeft(sib);
						sib = leftOf(parentOf(x));
					}
					setColor(sib, colorOf(parentOf(x)));
					setColor(parentOf(x), BLACK);
					setColor(leftOf(sib), BLACK);
					rotateRight(parentOf(x));
					x = root;
				}
			}
		}
		setColor(x, BLACK);
	}

	private void decrementSize() {
		size--;
	}

	/*
	 * Returns the successor of the specified Entry, or null if no such.
	 */
	private Node successor(Node t) {
		if (t == null) {
			return null;
		} else if (t.right != null) {
			Node p = t.right;
			while (p.left != null) {
				p = p.left;
			}
			return p;
		} else {
			Node p = t.parent;
			Node ch = t;
			while (p != null && ch == p.right) {
				ch = p;
				p = p.parent;
			}
			return p;
		}
	}

    /*
     * -----------------------------------------
     */
    
    // --------------------- FINITIZATION ------------------------//
    public static IFinitization finRedBlackTree(int size) {
        return finRedBlackTree(size, size, 0, size - 1);
    }

    public static IFinitization finRedBlackTree(int numEntries, int maxSize,int minKey, int maxKey) {
        IFinitization f = FinitizationFactory.create(RedBlackTree.class);

        IClassDomain entryDomain = f.createClassDomain(Node.class, numEntries);
        IObjSet entries = f.createObjSet(Node.class, true);
        entries.addClassDomain(entryDomain);

        IIntSet sizes = f.createIntSet(0, maxSize);

        IIntSet keys = f.createIntSet(minKey, maxKey);

        IIntSet colors = f.createIntSet(0, 1);

        f.set("root", entries);
        f.set("size", sizes);
        f.set("Node.left", entries);
        f.set("Node.right", entries);
        f.set("Node.parent", entries);
        f.set("Node.color", colors);
        f.set("Node.key", keys);

        return f;

    }

    // --------------------- FINITIZATION ------------------------//

    // ------------------------ repOK ---------------------------//
    public boolean repOK() {
        if (root == null)
            return size == 0;
        // RootHasNoParent
        if (root.parent != null)
            return debug("RootHasNoParent");
        Set visited = new java.util.HashSet();
        visited.add(new Wrapper(root));
        java.util.LinkedList workList = new java.util.LinkedList();
        workList.add(root);
        while (!workList.isEmpty()) {
            Node current = (Node) workList.removeFirst();
            // Acyclic
            // // if (!visited.add(new Wrapper(current)))
            // // return debug("Acyclic");
            // Parent Definition
            Node cl = current.left;
            if (cl != null) {
                if (!visited.add(new Wrapper(cl)))
                    return debug("Acyclic");
                if (cl.parent != current)
                    return debug("parent_Input1");
                workList.add(cl);
            }
            Node cr = current.right;
            if (cr != null) {
                if (!visited.add(new Wrapper(cr)))
                    return debug("Acyclic");
                if (cr.parent != current)
                    return debug("parent_Input2");
                workList.add(cr);
            }
        }
        // SizeOk
        if (visited.size() != size)
            return debug("SizeOk");
        if (!repOkColors())
            return false;
        return repOkKeysAndValues();
    }

    private boolean repOkColors() {
        // RedHasOnlyBlackChildren
        java.util.LinkedList workList = new java.util.LinkedList();
        workList.add(root);
        while (!workList.isEmpty()) {
            Node current = (Node) workList.removeFirst();
            Node cl = current.left;
            Node cr = current.right;
            if (current.color == RED) {
                if (cl != null && cl.color == RED)
                    return debug("RedHasOnlyBlackChildren1");
                if (cr != null && cr.color == RED)
                    return debug("RedHasOnlyBlackChildren2");
            }
            if (cl != null)
                workList.add(cl);
            if (cr != null)
                workList.add(cr);
        }
        // SimplePathsFromRootToNILHaveSameNumberOfBlackNodes
        int numberOfBlack = -1;
        workList = new java.util.LinkedList();
        workList.add(new Pair(root, 0));
        while (!workList.isEmpty()) {
            Pair p = (Pair) workList.removeFirst();
            Node e = p.e;
            int n = p.n;
            if (e != null && e.color == BLACK)
                n++;
            if (e == null) {
                if (numberOfBlack == -1)
                    numberOfBlack = n;
                else if (numberOfBlack != n)
                    return debug("SimplePathsFromRootToNILHaveSameNumberOfBlackNodes");
            } else {
                workList.add(new Pair(e.left, n));
                workList.add(new Pair(e.right, n));
            }
        }
        return true;
    }

    private boolean repOkKeysAndValues() {
        // BST1 and BST2
        // this was the old way of determining if the keys are ordered
        // java.util.LinkedList workList = new java.util.LinkedList();
        // workList = new java.util.LinkedList();
        // workList.add(root);
        // while (!workList.isEmpty()) {
        // Entry current = (Entry)workList.removeFirst();
        // Entry cl = current.left;
        // Entry cr = current.right;
        // if (current.key==current.key) ;
        // if (cl != null) {
        // if (compare(current.key, current.maximumKey()) <= 0)
        // return debug("BST1");
        // workList.add(cl);
        // }
        // if (cr != null) {
        // if (compare(current.key, current.minimumKey()) >= 0)
        // return debug("BST2");
        // workList.add(cr);
        // }
        // }
        // this is the new (Alex's) way to determine if the keys are ordered
        if (!orderedKeys(root, null, null))
            return debug("BST");
        // touch values
        java.util.LinkedList workList = new java.util.LinkedList();
        workList.add(root);
        while (!workList.isEmpty()) {
            Node current = (Node) workList.removeFirst();

            if (current.left != null)
                workList.add(current.left);
            if (current.right != null)
                workList.add(current.right);
        }
        return true;
    }

    private boolean orderedKeys(Node e, Object min, Object max) {
        if (e.key == -1)
            return false;
        if (((min != null) && (compare(e.key, min) <= 0))
                || ((max != null) && (compare(e.key, max) >= 0)))
            return false;
        if (e.left != null)
            if (!orderedKeys(e.left, min, e.key))
                return false;
        if (e.right != null)
            if (!orderedKeys(e.right, e.key, max))
                return false;
        return true;
    }

    private final boolean debug(String s) {
        // System.out.println(s);
        return false;
    }

    private final class Pair {
        Node e;

        int n;

        Pair(Node e, int n) {
            this.e = e;
            this.n = n;
        }
    }

    private static final class Wrapper {
        Node e;

        Wrapper(Node e) {
            this.e = e;
        }

        public boolean equals(Object obj) {
            if (!(obj instanceof Wrapper))
                return false;
            return e == ((Wrapper) obj).e;
        }

        public int hashCode() {
            return System.identityHashCode(e);
        }
    }

    private int compare(Object k1, Object k2) {
        return ((Comparable) k1).compareTo(k2);
    }
}
