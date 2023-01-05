package stack.array;

import korat.finitization.IArraySet;
import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;
import stack.common.Overflow;
import stack.common.Underflow;



// StackAr class
//
// CONSTRUCTION: with or without a capacity; default is 10
//
// ******************PUBLIC OPERATIONS*********************
// void push( x )         --> Insert x
// void pop( )            --> Remove most recently inserted item
// Object top( )          --> Return most recently inserted item
// Object topAndPop( )    --> Return and remove most recently inserted item
// boolean isEmpty( )     --> Return true if empty; else false
// boolean isFull( )      --> Return true if full; else false
// void makeEmpty( )      --> Remove all items
// ******************ERRORS********************************
// Overflow and Underflow thrown as needed

/**
 * Array-based implementation of the stack.
 * @author Mark Allen Weiss
 */
public class StackAr implements java.io.Serializable
{

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
    //@ invariant theArray != null && theArray.length >= 0 && topOfStack >= -1 && topOfStack < theArray.length;
	 public boolean repOK() {
		 return theArray != null && theArray.length >= 0 && topOfStack >= -1 && topOfStack < theArray.length ;
	 }
	
	
    /**
     * Construct the stack.
     */
    public StackAr( )
    {
        this( DEFAULT_CAPACITY );
    }

    /**
     * Construct the stack.
     * @param capacity the capacity.
     */
    public StackAr( int capacity )
    {
        theArray = new Object[ capacity ];
        topOfStack = -1;
    }

    /**
     * Test if the stack is logically empty.
     * @return true if empty, false otherwise.
     */
    public boolean isEmpty( )
    {
        return topOfStack == -1;
    }

    /**
     * Test if the stack is logically full.
     * @return true if full, false otherwise.
     */
    public boolean isFull( )
    {
        return topOfStack == theArray.length - 1;
    }

    /**
     * Make the stack logically empty.
     */
    public void makeEmpty( )
    {
        topOfStack = -1;
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
        return theArray[ topOfStack ];
    }

    /**
     * Remove the most recently inserted item from the stack.
     * @exception Underflow if stack is already empty.
     */
    public void pop( ) throws Underflow
    {
        if( isEmpty( ) )
            throw new Underflow( );
        theArray[ topOfStack-- ] = null;
    }

    /**
     * Insert a new item into the stack, if not already full.
     * @param x the item to insert.
     * @exception Overflow if stack is already full.
     */
    //@ requires theArray.length > 0;
    //@ ensures theArray[topOfStack] == x;
    public void push( Object x ) throws Overflow
    {
        if( isFull( ) )
            throw new Overflow( );
        theArray[ ++topOfStack ] = x;
    }
    //@ requires theArray.length > 0;
    public void pushPop(Object x) throws Overflow {
        push(x);
        Object y = topAndPop();
        assert x == y;
    }

    /**
     * Return and remove most recently inserted item from the stack.
     * @return most recently inserted item, or null, if stack is empty.
     */
    public Object topAndPop( )
    {
        if( isEmpty( ) )
            return null;
        Object topItem = top( );
        theArray[ topOfStack-- ] = null;
        return topItem;
    }

    private Object [ ] theArray;
    private int        topOfStack;

    static final int DEFAULT_CAPACITY = 10;
    
    public static IFinitization finStackAr(int size) {
        return finStackAr(size, size);
    }
    
    
    public static IFinitization finStackAr(int maxArrayLength,
            int maxArrayValue) {
    	
    	int max = maxArrayLength-1;
	    IFinitization f = FinitizationFactory.create(StackAr.class);
	    
	    IIntSet arrayLength = f.createIntSet(0, 1, max);
	    
	    IObjSet elems = f.createObjSet(Integer.class);
        IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
        elemsClassDomain.includeInIsomorphismCheck(false);
        for (int i = 0; i <maxArrayValue; i++)
            elemsClassDomain.addObject(new Integer(i));
        elems.addClassDomain(elemsClassDomain);
	    elems.setNullAllowed(true);
		
        IIntSet sp = f.createIntSet(-1, 1, max-1);

	    IArraySet arrays = f.createArraySet(Object[].class, arrayLength, elems, 1);
	    f.set("theArray", arrays);
	    f.set("topOfStack", sp);
	    return f;
}
            
  
 /*   public static void main( String [ ] args )
    {
        StackAr s = new StackAr( 12 );

        Object[] o = new Object[15];
        System.out.println(o.length);
        
        
        try
        {
            for( int i = 0; i < 10; i++ )
                s.push( new Integer( i ) );
        }
        catch( Overflow e ) {
            System.out.println( "Unexpected overflow" );
        }

        while( !s.isEmpty( ) )
            System.out.println( s.topAndPop( ) );
    }*/
}
