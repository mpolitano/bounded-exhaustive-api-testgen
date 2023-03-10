package binarysearchtree;


// Basic node stored in unbalanced binary search trees
// Note that this class is not accessible outside
// of package DataStructures

public class BinaryNode implements java.io.Serializable 
{
    private static final long serialVersionUID = 1L;

    // Constructors
    BinaryNode( int theElement )
    {
        this( theElement, null, null);
    }

    BinaryNode( int theElement, BinaryNode lt, BinaryNode rt )
    {
        element  = theElement;
        left     = lt;
        right    = rt;
    }
    public BinaryNode() {
        this(-1);
    }

    // Friendly data; accessible by other package routines
    int element;      // The data in the node
    BinaryNode left;         // Left child
    BinaryNode right;        // Right child
}
