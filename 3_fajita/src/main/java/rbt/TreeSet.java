package rbt;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;


import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;
import korat.finitization.IClassDomain;


//Authors: Marcelo Frias
/**
 * @Invariant ( this.RED==false ) && 
 *		( this.BLACK==true ) &&
 *		( this.root.parent in null ) &&
 *		( this.root!=null => this.root.color = this.BLACK ) && 
 *		( all n: TreeSetEntry | n in this.root.*(left @+ right @+ parent) @- null => ( 
 *				(n.key != null ) &&
 *				( n.left != null => n.left.parent = n ) &&
 *				( n.right != null => n.right.parent = n ) &&
 *				( n.parent != null => n in n.parent.(left @+ right) ) &&
 *				( n !in n.^parent ) &&
 *				( all x : TreeSetEntry | (( x in n.left.^(left @+ right) @+ n.left @- null ) => ( n.key > x.key )) ) &&
 *				( all x : TreeSetEntry | (( x in n.right.^(left @+ right) @+ n.right @- null ) => ( x.key > n.key ))) &&
 *				( n.color = this.RED && n.parent != null => n.parent.color = this.BLACK ) && 
 *				
 *				( ( n.left=null && n.right=null ) => ( n.blackHeight=1 ) ) &&
 *				( n.left!=null && n.right=null => ( 
 *				      ( n.left.color = this.RED ) && 
 *				      ( n.left.blackHeight = 1 ) && 
 *				      ( n.blackHeight = 1 )  
 *				)) &&
 *				( n.left=null && n.right!=null =>  ( 
 *				      ( n.right.color = this.RED ) && 
 *				      ( n.right.blackHeight = 1 ) && 
 *				      ( n.blackHeight = 1 ) 
 *				 )) && 
 *				( n.left!=null && n.right!=null && n.left.color=this.RED && n.right.color=this.RED => ( 
 *				        ( n.left.blackHeight = n.right.blackHeight ) && 
 *				        ( n.blackHeight = n.left.blackHeight ) 
 *				)) && 
 *				( n.left!=null && n.right!=null && n.left.color=this.BLACK && n.right.color=this.BLACK => ( 
 *				        ( n.left.blackHeight=n.right.blackHeight ) && 
 *				        ( n.blackHeight=n.left.blackHeight + 1 )  
 *				)) && 
 *				( n.left!=null && n.right!=null && n.left.color=this.RED && n.right.color=this.BLACK => ( 
 *				        ( n.left.blackHeight=n.right.blackHeight + 1 ) && 
 *				        ( n.blackHeight = n.left.blackHeight  )  
 *				)) && 
 *				( n.left!=null && n.right!=null && n.left.color=this.BLACK && n.right.color=this.RED => ( 
 *				        ( n.right.blackHeight=n.left.blackHeight + 1 ) && 
 *				        ( n.blackHeight = n.right.blackHeight  )  )) 
 *				)) ; 
 */
public class TreeSet implements Serializable {
	
	//*************************************************************************
	//************************* From now on repOk  ****************************
	//*************************************************************************.

	
	/**
	 * 
	 */
	private static final long serialVersionUID = -5519672093028431423L;


	/***breadth first search TUNNEADO.:Take from Korat*/
	/**we do not ask for root be black.**/ /** wait, now we do! **/
	
	public boolean repOK() {
        if (root == null)
            return size == 0;
        if (root.parent != null)
            return false;
		
		// // Added by Nico to reconcile discrepancy with declarative invariant
		// if (root.color != 1)
		// 	return false;
		
        Set<Wrapper> visited = new java.util.HashSet<Wrapper>();
        visited.add(new Wrapper(root));
        java.util.LinkedList<TreeSetEntry> workList = new java.util.LinkedList<TreeSetEntry>();
        workList.addLast(root);
        while (!workList.isEmpty()) {
        	TreeSetEntry current = (TreeSetEntry) workList.removeFirst();
            // Acyclic
            // Parent Definition
        	TreeSetEntry cl = current.left;
            if (cl != null) {
                if (!visited.add(new Wrapper(cl)))
                    return false;
                if (cl.parent != current)
                    return false;
                workList.addLast(cl);
            }
            TreeSetEntry cr = current.right;
            if (cr != null) {
                if (!visited.add(new Wrapper(cr)))
                    return false;
                if (cr.parent != current)
                    return false;
                workList.addLast(cr);
            }
        }
        // SizeOk
        if (visited.size() != size)
            return false;
        	
        if (!repOK_Colors())
            return false;
        return repOK_KeysAndValues();
    }
    
    
    private static final class Wrapper {
    	TreeSetEntry e;

        Wrapper(TreeSetEntry e) {
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
    
    
	/***Breadth first search NO TUNNEADO.
    /**Take from JML specificacion with the exceptions: 
     * we do not ask for root be black.
     * We dont have blackheight attribute
     * We ask for the ordered key out of the main loop.
     * @return
     */
    public boolean repOKBFSNoTunning() { 
            HashSet<TreeSetEntry> allNodes = new HashSet<TreeSetEntry>();
            LinkedList<TreeSetEntry> queue = new LinkedList<TreeSetEntry>();
            //( this.root.parent in null )
            if(root!=null && root.parent !=null){
            	return false;
            }
            if (root != null)
                queue.add(root);
            while (!queue.isEmpty()) {
                    TreeSetEntry node = queue.removeFirst();
                    //(n.key != null )
              
                    //( n.left != null => n.left.parent = n )
                    if (node.left != null){
                    		if(node.left.parent!=node){
                    			return false;
                    		}
                            queue.addLast(node.left);
                    }  
                   // ( n.right != null => n.right.parent = n )
                    if (node.right != null){
                    		if(node.right.parent!=node){
                    			return false;
                    		}
                            queue.addLast(node.right);
                    }
                    //( n.parent != null => n in n.parent.(left @+ right) ) &&
                    if(node.parent!=null){
                    	if(node.parent.right != node && node.parent.left !=node)
                    		return false;
                    }
                    //( n !in n.^parent ) 
                    if (!allNodes.add(node))
                        return false; // Not acyclic

                    
                    
                //	( n.color = this.RED && n.parent != null => n.parent.color = this.BLACK )    
                    if(node.color ==RED && node.parent!=null){
                    	if(node.parent.color !=BLACK){
                    		return false;
                    	}
                    }
              }
            //entiendo que deberia estar afuera del ciclo
            if (!isOrdered(root))
                    return false;
           
        	int numberOfBlack = -1;
			LinkedList<Pair> workList2 = new LinkedList<Pair>();

			workList2.add(new Pair(root, 0));

			while (workList2.size() > 0) {
				Pair p = (Pair) workList2.get(0);
				workList2.remove(0);
				TreeSetEntry e = p.e;
				int n = p.n;
				if (e != null && e.color == BLACK)
					n++;
				if (e == null) {
					if (numberOfBlack == -1)
						numberOfBlack = n;
					else if (numberOfBlack != n)
						return false;
				} else {
					workList2.addLast(new Pair(e.left, n));
					workList2.addLast(new Pair(e.right, n));
				}
			}
            if (allNodes.size() != size)
                    return false; // Wrong size.

            return true;
    }
    
    
	private boolean isOrdered(TreeSetEntry n) {
		return n == null || isOrdered(n, -1, -1);
	}

	private boolean isOrdered(TreeSetEntry n, int min, int max) { 	
		if ((min != -1 && n.key <= (min)) || (max != -1 && n.key >= (max)))
            return false;
		if (n.left != null)
			if (!isOrdered(n.left, min, n.key))
				return false;
		if (n.right != null)
			if (!isOrdered(n.right, n.key, max))
				return false;
		return true;
	}
	
	
	
		public boolean repOK_Colors() {

			LinkedList<TreeSetEntry> workList = new LinkedList<TreeSetEntry>();
			workList.add(root);
			while (workList.size() > 0) {
				TreeSetEntry current = (TreeSetEntry) workList.get(0);
				workList.remove(0);
				TreeSetEntry cl = current.left;
				TreeSetEntry cr = current.right;
				if (current.color == RED) {
					if (cl != null && cl.color == RED)
						return false;
					if (cr != null && cr.color == RED)
						return false;
				}
				if (cl != null)
					workList.addLast(cl);
				if (cr != null)
					workList.addLast(cr);
			}

			int numberOfBlack = -1;
			LinkedList<Pair> workList2 = new LinkedList<Pair>();

			workList2.add(new Pair(root, 0));

			while (workList2.size() > 0) {
				Pair p = (Pair) workList2.get(0);
				workList2.remove(0);
				TreeSetEntry e = p.e;
				int n = p.n;
				if (e != null && e.color == BLACK)
					n++;
				if (e == null) {
					if (numberOfBlack == -1)
						numberOfBlack = n;
					else if (numberOfBlack != n)
						return false;
				} else {
					workList2.addLast(new Pair(e.left, n));
					workList2.addLast(new Pair(e.right, n));
				}
			}
			return true;
		}

		
		public boolean repOK_orderedKeys(TreeSetEntry e, int min, int max) {

			if ((e.key <= min) || (e.key >= max))
				return false;
			if (e.left != null)
				if (!repOK_orderedKeys(e.left, min, e.key))
					return false;

			if (e.right != null)
				if (!repOK_orderedKeys(e.right, e.key, max))
					return false;
			return true;
		}

		public boolean repOK_KeysAndValues() {
			int min = repOK_findMin(root);
			int max = repOK_findMax(root);
			if (!repOK_orderedKeys(root, min-1, max+1))
				return false;

			return true;
		}

		private int repOK_findMin(TreeSetEntry root) {
			TreeSetEntry curr = root;
			while (curr.left!=null) {
				curr = curr.left;
			}
			return curr.key;
		}

		private int repOK_findMax(TreeSetEntry root) {
			TreeSetEntry curr = root;
			while (curr.right!=null) {
				curr = curr.right;
			}
			return curr.key;
		}
		
		
	/****************repOK con alguna parte de la estructura fija******************/
	/******************************************************************************/
	/******************************************************************************/	
		public boolean repOKBFS_11() {
			int count =0;
			if (root == null)
				return size == 0;

			//if (root.parent != null)
			//	return false;
			//HashSet<TreeSetEntry> visited = new HashSet<TreeSetEntry>();
			//visited.add(root);
			count++;
			LinkedList<TreeSetEntry> workList = new LinkedList<TreeSetEntry>();

			workList.add(root);

			while (workList.size() > 0) {

				TreeSetEntry current = (TreeSetEntry) workList.get(0);
				workList.remove(0);

				TreeSetEntry cl = current.left;
				if (cl != null) {
					count++;
					/*if (!visited.add(cl))
						return false;
					if (cl.parent != current)
						return false;
					workList.addLast(cl);*/
				}
				TreeSetEntry cr = current.right;
				if (cr != null) {
					count++;
					/*if (!visited.add(cr))
						return false;
					if (cr.parent != current)
						return false;
					workList.addLast(cr);*/
				}
			}

			if (/*visited.size()*/count != size)
				return false;

			//if (!repOK_Colors())
			//	return false;

			return repOK_KeysAndValues();
		}

		
		public boolean repOKBFS_2() {
			if (root == null)
				return size == 0;

			//if (root.parent != null)
			//	return false;
			//HashSet<TreeSetEntry> visited = new HashSet<TreeSetEntry>();
			//visited.add(root);
			//LinkedList<TreeSetEntry> workList = new LinkedList<TreeSetEntry>();

			//workList.add(root);

			//while (workList.size() > 0) {

			//	TreeSetEntry current = (TreeSetEntry) workList.get(0);
			//	workList.remove(0);

			//	TreeSetEntry cl = current.left;
			//	if (cl != null) {
					/*if (!visited.add(cl))
						return false;
					if (cl.parent != current)
						return false;
					workList.addLast(cl);*/
			//	}
			//	TreeSetEntry cr = current.right;
			//	if (cr != null) {
					/*if (!visited.add(cr))
						return false;
					if (cr.parent != current)
						return false;
					workList.addLast(cr);*/
			//	}
			//}

//			if (visited.size()!= size)
//				return false;

			//if (!repOK_Colors())
			//	return false;

			return repOK_KeysAndValues2();
		}
		
		
		public boolean repOK_KeysAndValues2() {
			int count =0;
			int min = repOK_findMin(root);
			int max = repOK_findMax(root);
			if (!repOK_orderedKeys(root, min-1, max+1))
				return false;

			// touch values
			LinkedList<TreeSetEntry> workList = new LinkedList<TreeSetEntry>();
			count++;
			workList.add(root);
			while (workList.size() > 0) {
				TreeSetEntry current = (TreeSetEntry) workList.get(0);
				workList.remove(0);

				if (current.left != null){
					count++;
					workList.addLast(current.left);
				}	
				if (current.right != null){
					count++;
					workList.addLast(current.right);
				}	
			}
			return count == size;//true;
		}
		
		public boolean repOKBFS_3() {
			if (root == null)
				return size == 0;

			if (root.parent != null)
				return false;
			//HashSet<TreeSetEntry> visited = new HashSet<TreeSetEntry>();
			//visited.add(root);
			LinkedList<TreeSetEntry> workList = new LinkedList<TreeSetEntry>();

			workList.add(root);

			while (workList.size() > 0) {

				TreeSetEntry current = (TreeSetEntry) workList.get(0);
				workList.remove(0);

				TreeSetEntry cl = current.left;
				if (cl != null) {
					//if (!visited.add(cl))
					//	return false;
					if (cl.parent != current)
						return false;
					workList.addLast(cl);
				}
				TreeSetEntry cr = current.right;
				if (cr != null) {
					//if (!visited.add(cr))
					//	return false;
					if (cr.parent != current)
						return false;
					workList.addLast(cr);
				}
			}

			//if (visited.size() != size)
			//	return false;

			if (!repOK_Colors())
				return false;

			return repOK_KeysAndValues();
		}
	
		

	public TreeSet() { } 
	/**
	 * parameter to be searched. This new attribute is 
	 * necessary since we want korat to generate
	 * all valid entries to test the search routine on SearchTree, 
	 * which are pairs of SearchTrees and integers.
	 */

	public TreeSet(TreeSetEntry r){
		root =r;
		size =1;
	}

	public /*@ nullable @*/ TreeSetEntry root = null;

	/**
	 * The number of entries in the tree
	 */
	public  int size = 0;

	/**
	 * The number of structural modifications to the tree.
	 */
	public transient int modCount = 0;



	//public /*static final */ boolean RED = false;
	//public /*static final */ boolean BLACK = true;

	private static final int RED = 0;
	private static final int BLACK = 1;


	public boolean contains(int aKey) {
		return getEntry(aKey) != null;
	}

	private TreeSetEntry getEntry(int key) {
		TreeSetEntry p = root;
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


	private TreeSetEntry getEntry_remove(int key) {
		TreeSetEntry p = root;
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


	private void init_TreeSetEntry(TreeSetEntry entry, int new_key, TreeSetEntry new_parent) {
		entry.color = BLACK;
		entry.left = null;
		entry.right = null;
		entry.key = new_key;
		entry.parent = new_parent;
	}


	public boolean add(int aKey) {
		TreeSetEntry t = root;

		if (t == null) {
			incrementSize();
			root = new TreeSetEntry();
			init_TreeSetEntry(root, aKey, null);

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
					t.left = new TreeSetEntry();
					init_TreeSetEntry(t.left, aKey, t);

					fixAfterInsertion(t.left);

					return false;
				}
			} else { // cmp > 0


				if (t.right != null) {
					t = t.right;
				} else {
					incrementSize();
					t.right = new TreeSetEntry();
					init_TreeSetEntry(t.right, aKey, t);
					fixAfterInsertion(t.right);
					return false;
				}
			}
		}
		return false;
	}

	private void incrementSize() {
		modCount++;
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

	private static /*boolean*/ int colorOf(TreeSetEntry p) {
		//boolean black = true;
		/*boolean*/int  result ;
		if (p==null)
			//result =black;
			result =BLACK;
		else
			result =p.color;
		return result;
	}

	private static TreeSetEntry parentOf(TreeSetEntry p) {
		TreeSetEntry result;
		if (p == null)
			result = null;
		else
			result = p.parent;

		return result;
	}

	private static void setColor(TreeSetEntry p, /*boolean*/ int c) {
		if (p != null)
			p.color = c;
	}

	private static TreeSetEntry leftOf(TreeSetEntry p) {
		TreeSetEntry result ;
		if (p == null)
			result = null;
		else
			result = p.left;
		return result;
	}

	private static TreeSetEntry rightOf(TreeSetEntry p) {
		TreeSetEntry result;
		if (p == null) 
			result = null;
		else
			result = p.right;
		return result;
	}

	/** From CLR **/
	private void rotateLeft(TreeSetEntry p) {
		TreeSetEntry r = p.right;
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
	private void rotateRight(TreeSetEntry p) {
		TreeSetEntry l = p.left;
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
	private void fixAfterInsertion(final TreeSetEntry entry) {
		TreeSetEntry x = entry;
		x.color = RED;

		while (x != null && x != root && x.parent.color == RED) {

			if (parentOf(x) == leftOf(parentOf(parentOf(x)))) {
				TreeSetEntry y = rightOf(parentOf(parentOf(x)));
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
				TreeSetEntry y = leftOf(parentOf(parentOf(x)));
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
		TreeSetEntry p = getEntry_remove(aKey);
		if (p == null) {
			return false;
		}


		deleteEntry(p);

		return true;
	}

	/**
	 * Delete node p, and then rebalance the tree.
	 */
	private void deleteEntry(TreeSetEntry p) {
		decrementSize();

		// If strictly internal, copy successor's element to p and then make p
		// point to successor.
		if (p.left != null && p.right != null) {
			TreeSetEntry s = successor(p);
			p.key = s.key;

			p = s;
		} // p has 2 children

		// Start fixup at replacement node, if it exists.
		TreeSetEntry replacement;
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
	private void fixAfterDeletion(final TreeSetEntry entry) {
		TreeSetEntry x = entry;

		while (x != root && colorOf(x) == BLACK) {

			if (x == leftOf(parentOf(x))) {
				TreeSetEntry sib = rightOf(parentOf(x));

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
				TreeSetEntry sib = leftOf(parentOf(x));

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
		modCount++;
		size--;
	}

	/*
	 * Returns the successor of the specified Entry, or null if no such.
	 */
	private TreeSetEntry successor(TreeSetEntry t) {
		if (t == null) {
			return null;
		} else if (t.right != null) {
			TreeSetEntry p = t.right;
			while (p.left != null) {
				p = p.left;
			}
			return p;
		} else {
			TreeSetEntry p = t.parent;
			TreeSetEntry ch = t;
			while (p != null && ch == p.right) {
				ch = p;
				p = p.parent;
			}
			return p;
		}
	}

	
	
	public static IFinitization finTreeSet(int numEntries) {
		return finTreeSet(numEntries, numEntries, 0, numEntries - 1);
	}
	
	public static IFinitization finTreeSet(int numEntries, int maxSize,int minKey, int maxKey) {
		IFinitization f = FinitizationFactory.create(TreeSet.class);

		IClassDomain entryDomain = f.createClassDomain(TreeSetEntry.class, numEntries);
		IObjSet entries = f.createObjSet(TreeSetEntry.class, true);
		entries.addClassDomain(entryDomain);
		entryDomain.includeInIsomorphismCheck(true);

		IIntSet sizes = f.createIntSet(0, maxSize);

		IIntSet colors = f.createIntSet(0, 1);

		IIntSet keys = f.createIntSet(minKey, maxKey);

		f.set("root", entries);
		f.set("size", sizes);
		
		f.set("TreeSetEntry.left", entries);
		f.set("TreeSetEntry.right", entries);
		f.set("TreeSetEntry.parent", entries);
		f.set("TreeSetEntry.color", colors);
		f.set("TreeSetEntry.key", keys);
		return f;

	}
	
	
	public String toString() {
		StringBuffer buf = new StringBuffer();
		buf.append(size);        
		buf.append("{");
		if (root != null)
			buf.append(root.toStrings());
		buf.append("}");
		return buf.toString();
	}
	
	
	
//	private static int search(int[] s, int value) throws IndexOutOfBoundsException{
//		int i =0;
//		int res = 0;
//		while(i<s.length && s[i]!=value){
//			i++;
//		}
//		if(s[i] != value){
//			throw new IndexOutOfBoundsException();
//		}else{ 
//			if(i ==(s.length -1)){
//				res =s[0];
//			}
//			else 
//				res =s[i+1];
//		}
//		return res;
//	} 
	
	
	
}
