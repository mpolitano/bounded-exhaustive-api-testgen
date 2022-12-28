package stack.list;

import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;
import stack.common.Underflow;

// StackLi class
//
// CONSTRUCTION: with no initializer
//
// ******************PUBLIC OPERATIONS*********************
// void push( x )         --> Insert x
// void pop( )            --> Remove most recently inserted item
// Object top( )          --> Return most recently inserted item
// Object topAndPop( )    --> Return and remove most recent item
// boolean isEmpty( )     --> Return true if empty; else false
// boolean isFull( )      --> Always returns false
// void makeEmpty( )      --> Remove all items
// ******************ERRORS********************************
// pop on empty stack

/**
 * List-based implementation of the stack.
 * @author Mark Allen Weiss
 */
public class StackLi implements java.io.Serializable{
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	
  //@ invariant isAcyclic();
	 public boolean repOK() {
		 return isAcyclic();
	 }
	
  
    /**
     * Construct the stack.
     */
    public StackLi( )
    {
        topOfStack = null;
    }

    /**
     * Test if the stack is logically full.
     * @return false always, in this implementation.
     */
    public boolean isFull( )
    {
        return false;
    }

    /**
     * Test if the stack is logically empty.
     * @return true if empty, false otherwise.
     */
    public boolean isEmpty( )
    {
        return topOfStack == null;
    }

    /**
     * Make the stack logically empty.
     */
    public void makeEmpty( )
    {
        topOfStack = null;
    }
    private boolean contains(Object e)
    {
        ListNode temp = topOfStack;
        while (temp != null)
        {
            if (e==temp.element)
            {
                return true;
            }
            temp = temp.next;
        }
        return false;
    }
    public boolean isAcyclic()
    {
        StackLi ll = new StackLi();
        ListNode temp = topOfStack;
        while (temp != null)
        {
            if (ll.contains(temp))
            {
                return false;
            }
            ll.topOfStack=new ListNode(temp,ll.topOfStack);
            temp = temp.next;
        }
        return true;
    }
    /**
     * Get the most recently inserted item in the stack.
     * Does not alter the stack.
     * @return the most recently inserted item in the stack, or null, if empty.
     */
    public Object top( )
    {
        if( isEmpty( ) )
            return null;
        return topOfStack.element;
    }

    /**
     * Remove the most recently inserted item from the stack.
     * @exception Underflow if the stack is empty.
     */
    public void pop( ) throws Underflow
    {
        if( isEmpty( ) )
            throw new Underflow( );
        topOfStack = topOfStack.next;
    }

    /**
     * Return and remove the most recently inserted item from the stack.
     * @return the most recently inserted item in the stack, or null, if empty.
     */
    public Object topAndPop( )
    {
        if( isEmpty( ) )
            return null;

        Object topItem = topOfStack.element;
        topOfStack = topOfStack.next;
        return topItem;
    }

    /**
     * Insert a new item into the stack.
     * @param x the item to insert.
     */
    //@ ensures topOfStack.element == x;
    public void push( Object x )
    {
        topOfStack = new ListNode( x, topOfStack );
    }

    private ListNode topOfStack;

    
    /*public static void main( String [ ] args )
    {
        StackLi s = new StackLi( );

        for( int i = 0; i < 10; i++ )
            s.push( new Integer( i ) );

        while( !s.isEmpty( ) )
            System.out.println( s.topAndPop( ) );
    }*/
    
    public static IFinitization finStackLi(int size) {
        return finStackLi(size, size, size, size);
    }
            
    public static IFinitization finStackLi(int minSize, int maxSize,
            int numEntries, int numElems) {
        IFinitization f = FinitizationFactory.create(StackLi.class);

        IObjSet entries = f.createObjSet(ListNode.class, true);
        entries.addClassDomain(f.createClassDomain(ListNode.class, numEntries));

        
        IObjSet elems = f.createObjSet(Integer.class);
        IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
        elemsClassDomain.includeInIsomorphismCheck(false);
        for (int i = 0; i <numElems; i++)
            elemsClassDomain.addObject(new Integer(i));
        elems.addClassDomain(elemsClassDomain);
//        elems.setNullAllowed(true);

        f.set("topOfStack", entries);
        f.set(ListNode.class, "element", elems);
        f.set(ListNode.class, "next", entries);
        return f;
    }

    
    
    
    
    
}
