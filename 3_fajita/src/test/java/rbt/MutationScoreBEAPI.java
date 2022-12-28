package rbt;

import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.assertTrue;

import java.util.Collection;

/**
 * Class to be used as input to PIT in order to compute mutation score from a set of objects obtained
 * by running BEAPI
 * @author fmolina
 */
public class MutationScoreBEAPI {

  private String objects_file = "/Users/fmolina/phd/software/be-benchmark/scripts/results-begen-serialize/9_taco/rbt.TreeSet/beapi/graph/builders/3/beapi-tests/objects.ser";
  private int bound = 3; 
  private int structures = 11;
  private Collection<Object> objects;
  
  // Objects are loaded every time each test is run
  @Before 
  public void load_objects() {
    try {
      objects = util.Deserializer.deserialize(objects_file);
    } catch (Exception e) {}
  }

  @Test
  public void test_add() {
    try {
      assertTrue(objects!=null && objects.size()==structures);
      for (Object o : objects) {
        TreeSet ts = (TreeSet)o;
        for (int i=0; i < bound; i++) {
          ts.add(i);
          assertTrue(ts.repOK());
        }
      } 
    } catch (Exception e) {
      assertTrue(0 < 0);
    }
  }

  @Test
  public void test_remove() {
    try {
      assertTrue(objects!=null && objects.size()==structures);
      for (Object o : objects) {
        TreeSet ts = (TreeSet)o;
        for (int i=0; i < bound; i++) {
          ts.remove(i);
          assertTrue(ts.repOK());
        }
      }
    } catch (Exception e) {
      assertTrue(0 < 0);
    }
  }

}
