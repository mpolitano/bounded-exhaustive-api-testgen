package korat.examples.binarytree;

import java.io.Serializable;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Random;
import java.util.Set;

import korat.finitization.IFinitization;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

/**
 * BinaryTree: binary tree implementation took from Korat. 
 * Added builders:
 *     - BinaryTree()
 *     - add(Element elem)
 */
public class BinaryTree implements Serializable {

	private static final long serialVersionUID = 1L;

    /*
     * Builders ---------------------------
     */
    public BinaryTree() {
        
    }

    public void add(Element elem) {
        
        if (elem==null)
            throw new IllegalArgumentException();
        
        size++;

        if (root == null) {
            root = new Node();
            root.element = elem;
            return;
        }
        Random rand = new Random();
        Node current = root;
        boolean leaveReached = false;
        while (!leaveReached) {
            if (current.left == null || current.right == null) {
                leaveReached = true;
            } else {
                if (rand.nextInt(2)==0) {
                    // The node must be inserted in the left side
                    current = current.left;
                } else {
                    // The node must be inserted in the right side
                    current = current.right;
                }
            }
        }

        Node n = new Node();
        n.element = elem;
        if (current.left == null) {
            // insert in left
            current.left = n;
        } else {
            // insert in right
            current.right = n;
        }
    }
    /*
     * -----------------------------------------
     */

	public class Node implements Serializable {

		private static final long serialVersionUID = 1L;
        Element element;
		Node left;
        Node right;
    }

    public class Element {
        private int i;
        public Element(int i) {
            this.i = i;
        }
    }

    private Node root;
    private int size;
    
    @SuppressWarnings("unchecked")
    public boolean repOK() {
        if (root == null)
            return size == 0;
        // checks that tree has no cycle
        Set visited = new HashSet();
        visited.add(root);
        LinkedList workList = new LinkedList();
        workList.add(root);
        while (!workList.isEmpty()) {
            Node current = (Node) workList.removeFirst();
            if (current.left != null) {
                if (!visited.add(current.left))
                    return false;
                workList.add(current.left);
            }
            if (current.right != null) {
                if (!visited.add(current.right))
                    return false;
                workList.add(current.right);
            }
        }
        // checks that size is consistent
        return (visited.size() == size);
    }

    public static IFinitization finBinaryTree(int size) {
        return finBinaryTree(size, size, size);
    }

    public static IFinitization finBinaryTree(int nodesNum, int minSize,
            int maxSize) {
        IFinitization f = FinitizationFactory.create(BinaryTree.class);
        IObjSet nodes = f.createObjSet(Node.class, nodesNum, true);
        f.set("root", nodes);
        f.set("size", f.createIntSet(minSize, maxSize));
        f.set("Node.left", nodes);
        f.set("Node.right", nodes);
        return f;
    }
}
