package avl3;

import org.junit.Test;

public class AvlTreeTest {
	
	  @Test
	  public void test1() throws Throwable {

	    AvlTree avlTree0 = new AvlTree();
	    avlTree0.insert((java.lang.Integer)0);
	    
	    // Check representation invariant.
	    org.junit.Assert.assertTrue("Representation invariant failed: Check rep invariant (method repOK) for avlTree0", avlTree0.repOK());

	  }

	  
	  @Test
	  public void test2() throws Throwable {

	    AvlTree avlTree0 = new AvlTree();
	    
	    // Check representation invariant.
	    org.junit.Assert.assertTrue("Representation invariant failed: Check rep invariant (method repOK) for avlTree0", avlTree0.repOK());

	  }
}
