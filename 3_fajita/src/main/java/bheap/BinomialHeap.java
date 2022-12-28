//
// Copyright (C) 2006 United States Government as represented by the
// Administrator of the National Aeronautics and Space Administration
// (NASA).  All Rights Reserved.
// 
// This software is distributed under the NASA Open Source Agreement
// (NOSA), version 1.3.  The NOSA has been approved by the Open Source
// Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
// directory tree for the complete NOSA document.
// 
// THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
// KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
// LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
// SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
// A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
// THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
// DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//
package bheap;


import java.util.ArrayList;

import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

//import kodkod.util.collections.IdentityHashSet;

/**
 * @SpecField nodes: set BinomialHeapNode from this.Nodes, this.nodes.child, this.nodes.sibling, this.nodes.parent  
 *                   | this.nodes = this.Nodes.*(child @+ sibling) @- null ;
 */
/**
 * @Invariant ( all n: BinomialHeapNode | ( n in this.Nodes.*(sibling @+ child) @- null => 
 *               ( ( n.parent!=null => n.key >= n.parent.key ) && 
 *               ( n.child!=null => n !in n.child.*(sibling @+ child) @- null ) && 
 *               ( n.sibling!=null => n !in n.sibling.*(sibling @+ child) @- null ) && 
 *               ( ( n.child !=null && n.sibling!=null ) => 
 *                 ( no m: BinomialHeapNode | ( m in n.child.*(child @+ sibling) @- null && 
 *                                              m in n.sibling.*(child @+ sibling) @- null )) ) && 
 *               ( n.degree >= 0 ) && 
 *               ( n.child=null => n.degree = 0 ) && 
 *               ( n.child!=null =>n.degree=#(n.child.*sibling @- null) ) && 
 *               ( #( ( n.child @+ n.child.child.*(child @+ sibling) ) @- null ) = #( ( n.child @+ n.child.sibling.*(child @+ sibling)) @- null ) ) && 
 *               ( n.child!=null => ( all m: BinomialHeapNode | ( m in n.child.*sibling@-null => m.parent = n ) ) ) && 
 *               ( ( n.sibling!=null && n.parent!=null ) => ( n.degree > n.sibling.degree ) ) ))) && 
 *               
 *            ( this.size = #(this.Nodes.*(sibling @+ child) @- null) ) && 
 *            ( all n: BinomialHeapNode | n in this.Nodes.*sibling @- null => 
 *               ( ( n.sibling!=null => n.degree < n.sibling.degree ) && 
 *               ( n.parent=null ) )) ;
 */
public class BinomialHeap implements java.io.Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 554705088418746406L;

	private/*@ nullable @*/BinomialHeapNode Nodes;

	private int size;

	public BinomialHeap() {
		Nodes = null;
		size = 0;
	}

	/**RepOk Breadth first NO TUNNEADO*/
	public boolean repOK() {
		if (size == 0)
			return (Nodes == null);
		if (Nodes == null)
			return false;
		java.util.Set<NodeWrapper> visited = new java.util.HashSet<NodeWrapper>();
		int degree_ = size;
		int rightDegree = 0;

		for (BinomialHeapNode current = Nodes; current != null; current = current.sibling) {

			/*( ( n.parent!=null => n.key >= n.parent.key ) && 
			 ( n.child!=null => n !in n.child.*(sibling @+ child) @- null ) && 
			( n.sibling!=null => n !in n.sibling.*(sibling @+ child) @- null ) */
			if(current.parent!=null){
				if(current.key <current.parent.key){
					return false;
				}
			}
			/**checks that the list has no cycle*/
			if (!visited.add(new NodeWrapper(current)))
				return false;
			if (!current.isTree(visited, null))
				return false;

			//( n.degree >= 0 ) && 
			//( n.child=null => n.degree = 0 ) && 
			if(current.degree <0){
				return false;
			} 
			if(current.child ==null){
				if(current.degree!=0){
					return false;
				}
			}

			//( n.child!=null =>n.degree=#(n.child.*sibling @- null) ) && 
			//( #( ( n.child @+ n.child.child.*(child @+ sibling) ) @- null ) = 
			//#( ( n.child @+ n.child.sibling.*(child @+ sibling)) @- null ) ) && 
			//( n.child!=null => ( all m: BinomialHeapNode | ( m in n.child.*sibling@-null => m.parent = n ) ) ) && 
			//( ( n.sibling!=null && n.parent!=null ) => ( n.degree > n.sibling.degree ) ) ))) && 

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

			//OJO!El JML no dice nada de keys ordenadas
			if (!current.isHeapified())
				return false;

		}
		/**checks that the total size is consistent*/
		//( this.size = #(this.Nodes.*(sibling @+ child) @- null) )
		if (visited.size() != size)
			return false;
		return degree_ ==0;
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

	/**------------repOK routine and related routines--------------*/

	/**
	 * checks that the current binomial heap satisfies 
	 * its representation invariants, which means
	 * checking that list of trees has no cycles, the 
	 * total size is consistent, the degrees of all trees are 
	 * binomial and the keys are heapified.
	 * @return true iff this binomialHeap satisfies the 
	 * corresponding representation invariants
	 */

	public static IFinitization finBinomialHeap(int size) {

		IFinitization f = FinitizationFactory.create(BinomialHeap.class);

		IClassDomain heapsDomain = f.createClassDomain(BinomialHeapNode.class, size);
		IObjSet heaps = f.createObjSet(BinomialHeapNode.class);
		heaps.setNullAllowed(true);
		heapsDomain.includeInIsomorphismCheck(true);
		heaps.addClassDomain(heapsDomain);

		
		f.set("Nodes", heaps);
		f.set("size", f.createIntSet(0, size));
		IObjSet keys = f.createObjSet(Integer.class);
		IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
		elemsClassDomain.includeInIsomorphismCheck(false);
		for (int i = 0; i <= size -1; i++)
			elemsClassDomain.addObject(new Integer(i));
		keys.addClassDomain(elemsClassDomain);
		keys.setNullAllowed(false);

		f.set(BinomialHeapNode.class, "child", heaps);
		f.set(BinomialHeapNode.class, "sibling", heaps);
		f.set(BinomialHeapNode.class, "parent", heaps);
		f.set(BinomialHeapNode.class, "key", f.createIntSet(0, size -1));
		f.set(BinomialHeapNode.class, "degree", f.createIntSet(0, size));
		
		
		return f;
	}


	/*private static int search(int[] s, int value) throws IndexOutOfBoundsException{
		int i =0;
		int res = 0;
		while(i<s.length && s[i]!=value){
			i++;
		}
		if(s[i] != value){
			throw new IndexOutOfBoundsException();
		}else{ 
			if(i ==(s.length -1)){
				res =s[0];
			}
			else 
				res =s[i+1];
		}
		return res;
	} */
	
	
	/*
	private static int count_nodes(BinomialHeap b0) {
		IdentityHashSet<BinomialHeapNode> already_visited = new IdentityHashSet<BinomialHeapNode>();
		IdentityHashSet<BinomialHeapNode> to_be_visited = new IdentityHashSet<BinomialHeapNode>();

		if (b0.Nodes != null)
			to_be_visited.add(b0.Nodes);

		while (!to_be_visited.isEmpty()) {
			BinomialHeapNode node = to_be_visited.iterator().next();
			to_be_visited.remove(node);
			already_visited.add(node);

			BinomialHeapNode parent = node.parent;
			BinomialHeapNode child = node.child;
			BinomialHeapNode sibling = node.sibling;

			if (parent != null && !already_visited.contains(parent)) {
				to_be_visited.add(parent);
			}
			if (child != null && !already_visited.contains(child)) {
				to_be_visited.add(child);
			}
			if (sibling != null && !already_visited.contains(sibling)) {
				to_be_visited.add(sibling);
			}

		}

		return already_visited.size();
	}
	 */



}
// end of class BinomialHeap
