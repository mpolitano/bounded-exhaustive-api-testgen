package java2.util2.linkedlist;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import utils.Config;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.io.BufferedWriter;
import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java2.util2.NoSuchElementException;
import java2.util2.hashmap.HashMap;

import java.util.concurrent.ThreadLocalRandom;
import java.util.stream.Stream;


public class LinkedListTest { 
    
	//Change with sedl 
	public static int scope;
	public static int literals;
	public static String pathFile;
	private static int count = 0;

	@BeforeAll
    static void initAll() {
    	Config.readEnvironmentVariables();
    	scope = Config.scope;
    	literals = Config.literals;
    	pathFile = "serialize/java2.util2.linkedlist.LinkedList/"+Config.scope+"/objects.ser";
    }
	
	@AfterAll
    static void afterAll() {
		File dir = new File("../scripts/reportBEAPI/java2.util2.linkedlist.LinkedList/"+Config.scope);
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
	public void addTest() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;
				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
				int oldSize = list.size();
				list.add(i);
				assertTrue(list.size() == oldSize+1);
				assertTrue(list.repOK());
				list = (LinkedList)nextObject(ois);
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
	public void iterTest() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;
				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
			try {	
				list.listIterator(i);
			} catch (IndexOutOfBoundsException e) {
				assertTrue(list.repOK());
			}
				list = (LinkedList)nextObject(ois);
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
	public void addTest1() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				int i = ThreadLocalRandom.current().nextInt(-1, literals + 1);
				int j = ThreadLocalRandom.current().nextInt(-1, literals + 1);

				int oldSize = 0;
				try {
					count++;
					oldSize = list.size();
					list.add(i,j);
				} catch (IndexOutOfBoundsException e) {
					assertTrue(list.repOK());
				}
//				assertTrue(list.size() == oldSize+1);
				assertTrue(list.repOK());
				list = (LinkedList)nextObject(ois);
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
	public void add_first_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
				count++;

		    	assumeTrue(i<list.size());
				int oldSize = list.size();
				list.add(i);
				assertTrue(list.size() == oldSize+1);
				assertTrue(list.repOK());
				list = (LinkedList)nextObject(ois);
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
	public void indexOf_Test() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;

				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
				list.lastIndexOf(i);
				assertTrue(list.repOK());
				list = (LinkedList)nextObject(ois);
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
	public void add_last_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;

				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
				list.lastIndexOf(i);
				assertTrue(list.repOK());
				list = (LinkedList)nextObject(ois);
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
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;

				list.clear();
				assertTrue(list.size() == 0);
				assertTrue(list.repOK());
				list = (LinkedList)nextObject(ois);
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
	public void clone_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;

				LinkedList list1 = (LinkedList) list.clone();
				assertTrue(list1.repOK());
				assertTrue(list.repOK());
//				assertTrue(list.equals(list1));
				list = (LinkedList)nextObject(ois);
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
	public void contains_Test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;

				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
				list.contains(i);
		    	assertTrue(list.repOK());
		    	list = (LinkedList)nextObject(ois);
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
//   	public void equals_test() {
//		FileInputStream fileTestUnit;
//	  	ObjectInputStream ois;
//		FileInputStream fileTestUnit1;
//	  	ObjectInputStream ois1;
//		try {
//			fileTestUnit= new FileInputStream(pathFile);
//			ois = new ObjectInputStream(fileTestUnit);
//			fileTestUnit1= new FileInputStream(pathFile);
//			ois1 = new ObjectInputStream(fileTestUnit);
//			LinkedList list = (LinkedList)nextObject(ois);
//			LinkedList list1 = (LinkedList)nextObject(ois);
//
//			while(list != null){
//				while(list1 != null){
//					count++;
//
//					int i = ThreadLocalRandom.current().nextInt(0, scope + 1);
//					list.equals(list1);
//			    	assertTrue(list.repOK());
//			    	assertTrue(list1.repOK());
//			    	list = (LinkedList)nextObject(ois);
//			    	list1 = (LinkedList)nextObject(ois1);
//				}
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
	
	@Test
   	public void get_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
					int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
					try {
						count++;

						list.get(i);
					}catch(IndexOutOfBoundsException e) {
				    	assertTrue(list.repOK());
					}
			    	assertTrue(list.repOK());
				
		    	list = (LinkedList)nextObject(ois);
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
   	public void getFirst_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				try {
					count++;

					list.getFirst();
				}catch(NoSuchElementException e) {
			    	assertTrue(list.repOK());
				}
		    	assertTrue(list.repOK());
		    
		    	list = (LinkedList)nextObject(ois);
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}
		
//    	assertTrue(obj.equals(list.get(0)));
    }
	
   	@Test
   	public void getLast_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				try {
					count++;

					Object obj=list.getLast();
				}catch(NoSuchElementException e) {
			    	assertTrue(list.repOK());
				}
		    	assertTrue(list.repOK());
		    
		    	list = (LinkedList)nextObject(ois);
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}		
//    	assertTrue(obj.equals(list.get(list.size()-1)));    
    }
	
   	@Test
   	public void addFirst_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
				count++;

				list.addFirst(i);;
		    	assertTrue(list.repOK());
				assumeTrue(list.contains(i));
		    	list = (LinkedList)nextObject(ois);
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
   	public void addLast_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
				count++;

				list.addLast(i);;
		    	assertTrue(list.repOK());
				assumeTrue(list.contains(i));
		    
		    	list = (LinkedList)nextObject(ois);
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
   	public void index_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
				count++;

		    	list.indexOf(i);
		    	assertTrue(list.repOK());
		    
		    	list = (LinkedList)nextObject(ois);
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
   	public void empty_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;

		    	list.isEmpty();
		    	assertTrue(list.repOK());
		    
		    	list = (LinkedList)nextObject(ois);
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
   	public void const_test() {
		count++;

    	LinkedList list1 = new LinkedList();
    	assertTrue(list1.repOK());
    }
	
   	@Test
   	public void remove_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				try {
					count++;

					Integer i = ThreadLocalRandom.current().nextInt(0, literals + 1);
					list.remove(i);
				} catch (IndexOutOfBoundsException e){
			    	assertTrue(list.repOK());
				}
		    	assertTrue(list.repOK());
		    	
		    	list = (LinkedList)nextObject(ois);
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
   	public void remove_first_test() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;

			    	if(list.size()>0) {
			    		Object first = list.get(0);
			        	Object obj=list.removeFirst();
			        	assertTrue(list.repOK());
			        	assertTrue(first.equals(obj));
			    	}
		    	list = (LinkedList)nextObject(ois);
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
   	public void removeLast_test() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
			    	if(list.size()>0) {
			    		Object last = list.get(list.size()-1);
			        	Object obj=list.removeLast();
			        	assertTrue(list.repOK());
			        	assertTrue(last.equals(obj));
			    	}
		    	list = (LinkedList)nextObject(ois);
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
   	public void set_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;

						int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
						if(i<list.size()){
							list.set(i,0);
					    	assertTrue(list.repOK());
				    		Object last = list.get(list.size()-1);
				        	Object obj=list.removeLast();
				        	assertTrue(list.repOK());
				        	assertTrue(last.equals(obj));
						}
				    	
		    	list = (LinkedList)nextObject(ois);
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
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;

				list.size();
		    	assertTrue(list.repOK());
		    	list = (LinkedList)nextObject(ois);
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
//	@MethodSource("provide_List_Int_Int_Parameters")
//   	public void sublist_test(LinkedList list,Integer i, Integer j) {
//    	assumeTrue(i>0 && j<list.size() && i<list.size());
//    	list.subList(i,j);
//    	assertTrue(list.repOK());
//    }
//	
	@Test
   	public void toarray_test() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			LinkedList list = (LinkedList)nextObject(ois);
			while(list != null){
				count++;

		    	Object[] lArray = list.toArray();
		    	assertTrue(list.repOK());
		    	list = (LinkedList)nextObject(ois);
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		 }

//    	assertTrue(lArray[0].equals(list.getFirst()));

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
