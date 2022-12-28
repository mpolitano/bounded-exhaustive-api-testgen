package java2.util2.treemap;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java2.util2.Comparator;
import java2.util2.Set;
import utils.Config;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.BufferedWriter;
import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;

import java.util.concurrent.ThreadLocalRandom;


public class TreeMapTest { 
    
	
	//Change with sedl 
	public static int scope;
	public static int literals;

	public static String pathFile;
	private static int count = 0;
	
	@BeforeAll
    static void initAll() {
    	Config.readEnvironmentVariables();
    	scope = Config.scope;
    	pathFile = "serialize/java2.util2.treemap.TreeMap/"+Config.scope+"/objects.ser";
    	literals = Config.literals;
    }

	@AfterAll
    static void afterAll() {
		File dir = new File("../scripts/reportBEAPI/java2.util2.treemap.TreeMap/"+Config.scope);
		 if (! dir.exists()){
		        dir.mkdir();            
		 }
        	File file = new File(dir + "/tests.txt");
            try{
                FileWriter fw = new FileWriter(file.getAbsoluteFile());
                BufferedWriter bw = new BufferedWriter(fw);
                bw.write(String.valueOf(count) );
                bw.close();
            }
            catch (IOException e){
                e.printStackTrace();
                System.exit(-1);
            }
	}

	
	@Test
	public void clear_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){
				count++;
				tmap.clear();
				assertTrue(tmap.size() == 0);
				assertTrue(tmap.repOK());
				tmap = (TreeMap)nextObject(ois);
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}
	}
	
//	@ParameterizedTest
//	@MethodSource("provide_TMap_Parameters")
//	public void clone_Test(TreeMap tmap) {
//		TreeMap tmap1 = (TreeMap) tmap.clone();
//		assertTrue(tmap1.repOK());
//		assertTrue(tmap.repOK());
//		assertTrue(tmap.equals(tmap1));
//	 }
	
	@Test
	public void comparator_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){
				count++;
				Comparator c =  tmap.comparator();
				assertTrue(tmap.repOK());
				tmap = (TreeMap)nextObject(ois);
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}

	 }
	
//	@Test
//	public void toString_Test() {
//		FileInputStream fileTestUnit;
//	  	ObjectInputStream ois;
//		try {
//			fileTestUnit= new FileInputStream(pathFile);
//			ois = new ObjectInputStream(fileTestUnit);
//			TreeMap tmap = (TreeMap)nextObject(ois);
//			while(tmap != null){
//				count++;
//				tmap.toString();
//				assertTrue(tmap.repOK());
//				tmap = (TreeMap)nextObject(ois);
//			}
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
//		 catch (ClassNotFoundException e) {
//		// TODO Auto-generated catch block
//		e.printStackTrace();
//		}
//
//	 }
	
	@Test
	public void constructor_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		TreeMap t = new TreeMap();

	 }
	
	
	
	@Test
	public void contains_key_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){
				count++;
				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
			  	tmap.containsKey(i);
		    	assertTrue(tmap.repOK());
				tmap = (TreeMap)nextObject(ois);
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}
	 }
	
	@Test
	public void contains_value_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){
				count++;
				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
			  	tmap.containsValue(i);
		    	assertTrue(tmap.repOK());
				tmap = (TreeMap)nextObject(ois);
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}

	 }
	
	public void entry_set_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){
				count++;
			  	Set s = tmap.entrySet();
		    	assertTrue(tmap.repOK());
				tmap = (TreeMap)nextObject(ois);
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}
	 }
	
/*	@ParameterizedTest
	@MethodSource("provide_TMap_TMap_Parameters")
   	public void equals_test(TreeMap tmap, TreeMap tmap1) {
    	tmap.equals(tmap1);
    	assertTrue(tmap.repOK());
    	assertTrue(tmap1.repOK());
    }
*/
	
	@Test
   	public void first_key_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){
				if(tmap.size()>0) {
					count++;
			    	Object k = (Object) tmap.firstKey();
			    	assertTrue(tmap.repOK());
			    	assertTrue(tmap.containsKey(k));

				}
		    	assertTrue(tmap.repOK());
				tmap = (TreeMap)nextObject(ois);


			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}	
    }
	
	
	
//	@ParameterizedTest
//	@MethodSource("provide_TMap_Int_Parameters")
//   	public void head_map_test(TreeMap tmap, Object i) {
//    	TreeMap tmap1 =  tmap.headMap(i);
//    	assertTrue(tmap.repOK());
//    	assertTrue(tmap1.repOK());   	
//    }
//	
	@Test
   	public void empty_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){

				count++;
				boolean p = tmap.isEmpty();
		    	assertTrue(tmap.repOK());
		    	assertTrue((p ==true && tmap.size() ==0) || (p ==false && tmap.size() !=0));
				tmap = (TreeMap)nextObject(ois);

			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}	
    }
	
	
//	@ParameterizedTest
//	@MethodSource("provide_TMap_Parameters")
//   	public void key_set_test(TreeMap tmap) {
//    	Set s = tmap.keySet();
//    	assertTrue(tmap.repOK());
//    	assertTrue(s.size() == tmap.size());
//    
//    }
	
	@Test
   	public void last_key_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){
				count++;
				Object k =null;
		    	if(tmap.size()>0) {
			    	k = (Object) tmap.lastKey();
			    	assertTrue(tmap.containsKey(k));
		    	}
		    	assertTrue(tmap.repOK());
				tmap = (TreeMap)nextObject(ois);

			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}	
    }
	
	@Test
	public void put_test() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){
				int key = ThreadLocalRandom.current().nextInt(0, literals + 1);
				int value = ThreadLocalRandom.current().nextInt(0, literals + 1);
				count++;
				int oldSize = tmap.size();
				boolean b = tmap.containsKey(key);
				
				tmap.put(key,0);
				
				assertTrue((!b && tmap.size() == oldSize+1) ||(b && tmap.size() == oldSize));
				assertTrue(tmap.repOK());
				assertTrue(tmap.containsKey(key) && tmap.containsValue(0));
				tmap = (TreeMap)nextObject(ois);

			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}	
		


	 }
	
	@Test
   	public void remove_test() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){
				int key = ThreadLocalRandom.current().nextInt(0, literals + 1);

				count++;
				tmap.remove(key);
		    	
		    	assertTrue(tmap.repOK());
		    	assertTrue(!tmap.containsKey(key));
				tmap = (TreeMap)nextObject(ois);

			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}	
		

    }
	
	@Test
   	public void size_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeMap tmap = (TreeMap)nextObject(ois);
			while(tmap != null){
				count++;

				int key = ThreadLocalRandom.current().nextInt(0, literals + 1);

		    	int s = tmap.size();
		       	assertTrue(tmap.repOK());
				assertTrue((s==0 && tmap.isEmpty()) ||(s!=0 && !tmap.isEmpty()));
				tmap = (TreeMap)nextObject(ois);

			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}	
		


    }
	
	
//	@ParameterizedTest
//	@MethodSource("provide_TMap_Int_Int_Parameters")
//	public void sub_map_test(TreeMap tmap, Object fromKey,Object toKey) {
//
//		assumeTrue((Integer)fromKey<=(Integer)toKey);
//	
//		TreeMap subTree = tmap.subMap(fromKey,toKey);
//		assertTrue(subTree.repOK());
//				
//	 }
	
//	@ParameterizedTest
//	@MethodSource("provide_TMap_Int_Parameters")
//	public void tail_map_test(TreeMap tmap, Object fromKey) {
//
//		assumeTrue(tmap.containsKey(fromKey));
//	
//		TreeMap subTree = tmap.tailMap(fromKey);
//		assertTrue(subTree.repOK());
//				
//	 }
	
//	@ParameterizedTest
//	@MethodSource("provide_TMap_Parameters")
//	public void value_test(TreeMap tmap) {
//
//		Collection l = tmap.values();
//		assertTrue(tmap.repOK());
//		assertTrue((l.isEmpty() && tmap.isEmpty()) || (!l.isEmpty() && !tmap.isEmpty()) );

//	 }
	
	
	
	

	public static Object nextObject(ObjectInputStream ois) throws ClassNotFoundException, IOException {
			try {
				return ois.readObject();
			} catch (EOFException eof) {
				return null;
			} catch (ClassNotFoundException e) {
				throw e;
			} catch (IOException e) {
				throw e;
			}
		}    
    
}
