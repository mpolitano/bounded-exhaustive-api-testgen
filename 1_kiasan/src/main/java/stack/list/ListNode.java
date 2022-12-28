package stack.list;

public class ListNode implements java.io.Serializable{
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
    public ListNode() {}
    // Constructors
    ListNode( Object theElement )
    {
        this( theElement, null );
    }

    ListNode( Object theElement, ListNode n )
    {
        element = theElement;
        next    = n;
    }

    // Friendly data; accessible by other package routines
    Object   element;
    ListNode next;
}
