package org.apache.commons.collections4.list;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

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
import java.util.Random;


public class NodeCachingLinkedListTest { 


	//Change with sedl 
	public static int scope;
	public static String pathFile;
	public static int literals;

	@BeforeAll
	static void initAll() {
		Config.readEnvironmentVariables();
		scope = Config.scope;
		pathFile = "serialize/org.apache.commons.collections4.list.NodeCachingLinkedList/"+scope+"/randoop.ser";
		literals = Config.literals;
	}

	static int count;

	@BeforeEach
	void initCount() {
		count = 0;
	}

	@AfterEach
	void showCount() {
		System.out.println("Test:" + count); 
	}

	
	@AfterAll
    static void afterAll() {
		File dir = new File("../scripts/reportBEAPI/org.apache.commons.collections4.list.NodeCachingLinkedList/"+Config.literals);
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
	public void cont_test() {

		NodeCachingLinkedList ncl = new NodeCachingLinkedList();
		ncl = new NodeCachingLinkedList(100);

	}
	
	@Test
	public void getNodeFromCache_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;
				ncl.getNodeFromCache();
				assertTrue(ncl.repOK());
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	public void createNode_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;
				Random r = new Random();
				int i = r.nextInt(literals);	

				ncl.createNode(i);
				assertTrue(ncl.repOK());
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	public void clear_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;
				ncl.clear();
				assertTrue(ncl.repOK());
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	public void add_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;
				Random r = new Random();
				int i = r.nextInt(literals);	

				int oldSize = ncl.size();
				ncl.add(i);
				assertTrue(ncl.repOK());
				assertTrue(ncl.contains(i));
				assertTrue(ncl.size()== oldSize +1);

				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	public void get_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;
				Random r = new Random();
				int i = r.nextInt(literals);	


				//assumeTrue(i<ncl.size());
				if(i<ncl.size()) {
					Integer o = (Integer)ncl.get(i);
					assertTrue(ncl.repOK());
					assertTrue(ncl.contains(o));

				}

				ncl = (NodeCachingLinkedList)nextObject(ois);

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

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;

				Integer o = (Integer)ncl.size();
				assertTrue(ncl.repOK());

				ncl = (NodeCachingLinkedList)nextObject(ois);

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

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;

				boolean o = ncl.isEmpty();
				assertTrue(ncl.repOK());

				ncl = (NodeCachingLinkedList)nextObject(ois);

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
//	public void index_of_test() {
//
//		FileInputStream fileTestUnit;
//		ObjectInputStream ois;
//		try {
//			fileTestUnit= new FileInputStream(pathFile);
//			ois = new ObjectInputStream(fileTestUnit);
//
//			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
//			while(ncl != null){
//				count++;
//				Random r = new Random();
//				int value = r.nextInt(scope);	
//
//				Integer index = ncl.indexOf(value);
//				assertTrue(ncl.repOK());
//				assertTrue( (ncl.contains(value) && index >0 && index < ncl.size())||
//						(!ncl.contains(value) && index == -1));
//
//
//				ncl = (NodeCachingLinkedList)nextObject(ois);
//
//			}
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
//		catch (ClassNotFoundException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}

//	}



	//org.apache.commons.collections4.list.AbstractLinkedList.contains(java.lang.Integer)

	@Test
	public void contains_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;
				Random r = new Random();
				int value = r.nextInt(literals);	

				boolean b = ncl.contains(value);
				assertTrue(ncl.repOK());

				ncl = (NodeCachingLinkedList)nextObject(ois);

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


	//org.apache.commons.collections4.list.AbstractLinkedList.getFirst()
	@Test
	public void getfirst_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;

				if(ncl.size()>0) {
					Integer b = ncl.getFirst();
					assertTrue(ncl.repOK());
					assertTrue(ncl.contains(b));
				}
				ncl = (NodeCachingLinkedList)nextObject(ois);

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


	//org.apache.commons.collections4.list.AbstractLinkedList.getLast()
	@Test
	public void getlast_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;

				if(ncl.size()>0) {
					Integer b = ncl.getLast();
					assertTrue(ncl.repOK());
					assertTrue(ncl.contains(b));
				}
				ncl = (NodeCachingLinkedList)nextObject(ois);

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

	//org.apache.commons.collections4.list.AbstractLinkedList.addFirst(java.lang.Integer)

	@Test
	public void addFirst_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				Random r = new Random();
				int value = r.nextInt(literals);
				
				count++;

				int oldSize = ncl.size();
				ncl.addFirst(value);
				assertTrue(ncl.repOK());
				assertTrue(ncl.contains(value));
				assertTrue(ncl.size()== oldSize +1);
				
				
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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

	
	//org.apache.commons.collections4.list.AbstractLinkedList.addLast(java.lang.Integer)

	@Test
	public void addLast_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				Random r = new Random();
				int value = r.nextInt(literals);
				
				count++;

				
				int oldSize = ncl.size();
				ncl.addLast(value);
				assertTrue(ncl.repOK());
				assertTrue(ncl.contains(value));
				assertTrue(ncl.size()== oldSize +1);
				
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	
	
	//org.apache.commons.collections4.list.NodeCachingLinkedList.getMaximumCacheSize()

	@Test
	public void getMaximumCacheSize_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;

				
				Integer b = ncl.getMaximumCacheSize();
				assertTrue(ncl.repOK());
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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

	//org.apache.commons.collections4.list.NodeCachingLinkedList.isCacheFull()
	@Test
	public void isCacheFull_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;

				
				boolean b = ncl.isCacheFull();
				assertTrue(ncl.repOK());

				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	//org.apache.commons.collections4.list.AbstractLinkedList.lastIndexOf(java.lang.Integer)
	@Test
	public void lastIndexOf_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				Random r = new Random();
				int value = r.nextInt(literals);
				
				count++;

				
				int index = ncl.lastIndexOf(value);
				assertTrue(ncl.repOK());
				assertTrue((ncl.contains(value) && index >=0) ||  (!ncl.contains(value) && index ==-1) );
				
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	
	//org.apache.commons.collections4.list.AbstractLinkedList.remove(int)
	@Test
	public void remove_index_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				Random r = new Random();
				int index = r.nextInt(literals);
				
				count++;

				if(index > 0 && index < ncl.size()) {
					int oldSize = ncl.size();
					Integer b = ncl.remove(index);
					assertTrue(ncl.repOK());
					assertTrue(ncl.size() == oldSize-1);

				}
				ncl = (NodeCachingLinkedList)nextObject(ois);

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

	
	//org.apache.commons.collections4.list.AbstractLinkedList.remove(java.lang.Integer)
	
	@Test
	public void remove_value_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				Random r = new Random();
				int value = r.nextInt(literals);
				
				count++;

				int oldSize = ncl.size();
				boolean b = ncl.remove(new Integer(value));
				assertTrue(ncl.repOK());
				assertTrue((b && ncl.size() == oldSize-1) || (!b && ncl.size() == oldSize));

				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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

	//org.apache.commons.collections4.list.AbstractLinkedList.removeFirst()
	@Test
	public void removeFirst_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				Random r = new Random();
				int value = r.nextInt(literals);
				
				count++;

				if(ncl.size() > 0) {
					int oldSize = ncl.size();
					Integer b = ncl.removeFirst();
					assertTrue(ncl.repOK());
					assertTrue(ncl.size() == oldSize-1);
				}
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	
	

	//org.apache.commons.collections4.list.AbstractLinkedList.removeLast()
	
	@Test
	public void removeLast_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				
				
				count++;

				if(ncl.size() > 0) {
					int oldSize = ncl.size();
					Integer b = ncl.removeLast();
					assertTrue(ncl.repOK());
					assertTrue(ncl.size() == oldSize-1);
				}
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	

	//org.apache.commons.collections4.list.AbstractLinkedList.add(int,java.lang.Integer)
	@Test
	public void add_on_position_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				Random r = new Random();
				int value = r.nextInt(literals);
				
				int index = r.nextInt(literals);
				
				
				count++;

				if(index >0 && index <= ncl.size()) {
					int oldSize = ncl.size();
					ncl.add(index, value);
					assertTrue(ncl.repOK());
					assertTrue(ncl.size() == oldSize+1);
				}
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	
	//org.apache.commons.collections4.list.AbstractLinkedList.set(int,java.lang.Integer)
	@Test
	public void set_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				Random r = new Random();
				int value = r.nextInt(literals);
				
				int index = r.nextInt(literals);
				
				
				count++;

				if(index >0 && index < ncl.size()) {
					int oldSize = ncl.size();
					ncl.set(index, value);
					assertTrue(ncl.repOK());
					assertTrue(ncl.size() == oldSize);
					assertTrue(ncl.contains(value));
				}
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	//org.apache.commons.collections4.list.NodeCachingLinkedList.removeAllNodes()
	@Test
	public void removeAllNodes_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				count++;

				
				ncl.removeAllNodes();
				assertTrue(ncl.repOK());
				assertTrue(ncl.isEmpty());
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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

	
	
	//org.apache.commons.collections4.list.NodeCachingLinkedList.setMaximumCacheSize(int)
	@Test
	public void setMaximumCacheSize_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				Random r = new Random();
				int value = r.nextInt(literals);
				
				count++;

				ncl.setMaximumCacheSize(value);
				assertTrue(ncl.repOK());
			
				
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	//org.apache.commons.collections4.list.AbstractLinkedList.toArray()
	
	@Test
	public void toArray_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				
				count++;
				int size = ncl.size();
				Integer [] a = ncl.toArray();
				assertTrue(ncl.repOK());
				assertTrue(a.length == size);
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	
	//org.apache.commons.collections4.list.AbstractLinkedList.toArray([Ljava.lang.Integer;)

	@Test
	public void toArray2_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				
				count++;
				int size = ncl.size();
				Integer [] a = new Integer[ncl.size()];
				a = ncl.toArray(a);
				assertTrue(ncl.repOK());
				assertTrue(a.length == size);
				
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	//org.apache.commons.collections4.list.NodeCachingLinkedList.shrinkCacheToMaximumSize()
	@Test
	public void shrinkCacheToMaximumSize_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				
				count++;
				ncl.shrinkCacheToMaximumSize();
				assertTrue(ncl.repOK());

				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	

	
	//org.apache.commons.collections4.list.AbstractLinkedList.iterator()
	@Test
	public void Iterator_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				
				count++;
				java.util.Iterator i = ncl.iterator();
				assertTrue(ncl.repOK());

				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	
	
	//org.apache.commons.collections4.list.AbstractLinkedList.listIterator()
	@Test
	public void ListIterator_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				
				count++;
				org.apache.commons.collections4.ListIterator i = ncl.listIterator();
				assertTrue(ncl.repOK());

				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	
	
	//org.apache.commons.collections4.list.AbstractLinkedList.listIterator(int)
	@Test
	public void ListIterator_Int_test() {

		FileInputStream fileTestUnit;
		ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);

			NodeCachingLinkedList ncl = (NodeCachingLinkedList)nextObject(ois);
			while(ncl != null){
				
				Random r = new Random();
				int i = r.nextInt(literals);
				
				count++;
				if(i<ncl.size()) {
					org.apache.commons.collections4.ListIterator listIter = ncl.listIterator(i);
					assertTrue(ncl.repOK());
				}
				ncl = (NodeCachingLinkedList)nextObject(ois);

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
	
	
	//org.apache.commons.collections4.list.NodeCachingLinkedList.toString()
	//org.apache.commons.collections4.list.AbstractLinkedList.equals(java.lang.Object)


	
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
