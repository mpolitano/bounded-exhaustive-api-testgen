package java2.util2.treeset;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java2.util2.linkedlist.LinkedList;
import utils.Config;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import java.io.BufferedWriter;
import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.util.NoSuchElementException;
import java.util.concurrent.ThreadLocalRandom;
import java.util.stream.Stream;


public class TreeSetTest { 
    
	
	//Change with sedl 
		public static int scope;
		public static String pathFile;
		private static int count = 0;

		@BeforeAll
	    static void initAll() {
	    	Config.readEnvironmentVariables();
	    	scope = Config.scope;
	    	pathFile = "serialize/java2.util2.treeset.TreeSet/"+Config.scope+"/objects.ser";
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
		public void cont_Test() {
			TreeSet t = new TreeSet();
		}
		@Test
		public void add_Test() {
			
			FileInputStream fileTestUnit;
		  	ObjectInputStream ois;
			try {
				fileTestUnit= new FileInputStream(pathFile);
				ois = new ObjectInputStream(fileTestUnit);
				TreeSet tset = (TreeSet)nextObject(ois);
				while(tset != null){
					count++;
					int i = ThreadLocalRandom.current().nextInt(0, scope + 1);
	
					int oldSize = tset.size();
					boolean b = tset.contains(i);
					
					tset.add(i);
					
					assertTrue((!b && tset.size() == oldSize+1) ||(b && tset.size() == oldSize));
					assertTrue(tset.repOK());
					assertTrue(tset.contains(i));
					assertTrue(tset.size()>oldSize);

					tset = (TreeSet)nextObject(ois);

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
		public void clear_Test() {
			FileInputStream fileTestUnit;
		  	ObjectInputStream ois;
			try {
				fileTestUnit= new FileInputStream(pathFile);
				ois = new ObjectInputStream(fileTestUnit);
				TreeSet tset = (TreeSet)nextObject(ois);
				while(tset != null){
					count++;
					tset.clear();
					assertTrue(tset.size() == 0);
					assertTrue(tset.repOK());
					tset = (TreeSet)nextObject(ois);
	
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
	
	
//		@Test
//	public void comparator_Test() {
//		FileInputStream fileTestUnit;
//	  	ObjectInputStream ois;
//		try {
//			fileTestUnit= new FileInputStream(pathFile);
//			ois = new ObjectInputStream(fileTestUnit);
//			TreeSet tset = (TreeSet)nextObject(ois);
//			while(tset != null){
//				count++;
//				tset.comparator();
//				assertTrue(tset.repOK());
//				tset = (TreeSet)nextObject(ois);
//
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
	public void contain_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeSet tset = (TreeSet)nextObject(ois);
			while(tset != null){
				count++;
				int i = ThreadLocalRandom.current().nextInt(0, scope + 1);

				tset.contains(i);
				assertTrue(tset.repOK());
				tset = (TreeSet)nextObject(ois);

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
	public void first_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeSet tset = (TreeSet)nextObject(ois);
			while(tset != null){

				try {
				count++;
				Object k = (Object) tset.first();
				}catch(NoSuchElementException e) {
			    	assertTrue(tset.repOK());

				}
		    	
				tset = (TreeSet)nextObject(ois);

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
//	public void empty_Test() {
//		FileInputStream fileTestUnit;
//	  	ObjectInputStream ois;
//		try {
//			fileTestUnit= new FileInputStream(pathFile);
//			ois = new ObjectInputStream(fileTestUnit);
//			TreeSet tset = (TreeSet)nextObject(ois);
//			while(tset != null){
//				count++;
//				boolean p = tset.isEmpty();
//		    	assertTrue(tset.repOK());
//		    	assertTrue((p ==true && tset.size() ==0) || (p ==false && tset.size() !=0));
//		    	
//				tset = (TreeSet)nextObject(ois);
//
//			}
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
//		 catch (ClassNotFoundException e) {
//		// TODO Auto-generated catch block
//		e.printStackTrace();
//		}
//    }
//	
	@Test
   	public void size_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeSet tset = (TreeSet)nextObject(ois);
			while(tset != null){
				count++;
				int s = tset.size();
		       	assertTrue(tset.repOK());

				tset = (TreeSet)nextObject(ois);

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
//	
	@Test
   	public void last_test() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			TreeSet tset = (TreeSet)nextObject(ois);
			while(tset != null){
				if(tset.size()>0) {
					count++;

					try {
						count++;
						Object k = (Object) tset.last();
						}catch(NoSuchElementException e) {
					    	assertTrue(tset.repOK());

						}

				}
				tset = (TreeSet)nextObject(ois);

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
			TreeSet tset = (TreeSet)nextObject(ois);
			while(tset != null){
					count++;
					int i = ThreadLocalRandom.current().nextInt(0, scope + 1);

					tset.remove(i);
			    	assertTrue(tset.repOK());
			    	assertTrue(!tset.contains(i));

			    	tset = (TreeSet)nextObject(ois);

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
	
	
	
	/*
	 * Providers..
	 */
	
	
	

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
