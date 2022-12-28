package bintree1;

import java.util.HashSet;
import java.util.Set;

// Node must not implement Comparable interface...
@SuppressWarnings("unchecked")
public class Node  implements java.io.Serializable {
    
    private static final long serialVersionUID = 1L;

    public Node left; // left child

    public Node right; // right child

    public Integer info; // data

    public Node(Node left, Node right, int info) {
        this.left = left;
        this.right = right;
        this.info = info;
    }

    public Node(int info) {
        this.info = info;
    }

    public Node() {

    }

    @Override
    public String toString() {
        return "Node [left=" + left + ", right=" + right + ", info=" + info + "]";
    }

    

}
