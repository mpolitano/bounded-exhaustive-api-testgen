package korat.examples.fibheap;

import org.junit.Test;
import korat.examples.fibheap.FibonacciHeap;
import static org.junit.Assert.assertTrue;

public class FibHeapTest {

  @Test
  public void test_insert1() {
    FibonacciHeap fh = new FibonacciHeap();
    fh.insert(1);
    assertTrue(fh.repOK());
    fh.insert(2);
    fh.insert(-1);
    assertTrue(fh.repOK());
  }
}
