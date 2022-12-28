package builders;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.BufferedWriter;
import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;

import java.util.concurrent.ThreadLocalRandom;


import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;


import utils.Config;

public class ScheduleTest {

	//Change with sedl 
		public static int scope;
		public static String pathFile;
		private static int count = 0;
		public static int literals;

	    @BeforeAll
	    static void initAll() {
	    	Config.readEnvironmentVariables();
	    	scope = Config.scope;
	    	pathFile = "serialize/builders.Schedule/"+Config.scope+"/objects.ser";
	    	literals = Config.literals;
	    }
	
		@AfterAll
	    static void afterAll() {
			File dir = new File("../scripts/reportBEAPI/builders.Schedule/"+Config.scope);
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
	public void test_init() {
		Schedule sch = new Schedule();
		assertTrue(sch.repOK());
	}
	
//	@ParameterizedTest
//	@MethodSource("provide_Int_Int_Int_Parameters")
	    @Test
	    public void test_init1() {
		Schedule sch = new Schedule(1,1,1);
		assertTrue(sch.repOK());
	}
	
	   @Test
		public void test_add() {
	
			FileInputStream fileTestUnit;
		  	ObjectInputStream ois;
			try {
				fileTestUnit= new FileInputStream(pathFile);
				ois = new ObjectInputStream(fileTestUnit);
				Schedule sch = (Schedule)nextObject(ois);
				while(sch != null){
					count++;
					int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
					
					try {
						sch.addProcess(i);
					} catch (java.lang.IllegalArgumentException e) {
						assertTrue(sch.repOK());       
					}
					assertTrue(sch.repOK());
	
					sch = (Schedule)nextObject(ois);
	
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
	public void test_block() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			Schedule sch = (Schedule)nextObject(ois);
			while(sch != null){
				count++;
				int i = ThreadLocalRandom.current().nextInt(0, literals + 1);
				
				
				sch.blockProcess();
				assertTrue(sch.repOK());
				sch = (Schedule)nextObject(ois);

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
	public void test_initPrioQueue_good() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			Schedule sch = (Schedule)nextObject(ois);
			while(sch != null){
				count++;
				int i = ThreadLocalRandom.current().nextInt(-2, literals + 1);
				int j = ThreadLocalRandom.current().nextInt(-2, literals + 1);

				try {
					sch.initPrioQueue(j,i);
			} catch (java.lang.IllegalArgumentException e) {
				assertTrue(sch.repOK());
			}
			assertTrue(sch.repOK());
				sch = (Schedule)nextObject(ois);

			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
		}
		
		//workaround for stream stackoverflow
	

	}
	
	   @Test
	public void test_initPrioQueue_bad() {
			
			
			FileInputStream fileTestUnit;
		  	ObjectInputStream ois;
			try {
				fileTestUnit= new FileInputStream(pathFile);
				ois = new ObjectInputStream(fileTestUnit);
				Schedule sch = (Schedule)nextObject(ois);
				while(sch != null){
					count++;
					int i = ThreadLocalRandom.current().nextInt(-2, literals + 1);
					int j = ThreadLocalRandom.current().nextInt(-2, literals + 1);
					try {
						sch.initPrioQueue(i,i);
					} catch (java.lang.IllegalArgumentException e) {
						assertTrue(sch.repOK());
					}
						assertTrue(sch.repOK());
						sch = (Schedule)nextObject(ois);

				}
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			 catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			}
			
			//workaround for stream stackoverflow
		

		}
		
	   @Test
	public void test_finishAll() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			Schedule sch = (Schedule)nextObject(ois);
			while(sch != null){
				count++;
				try {
					
					sch.finishAllProcesses();
					assertTrue(sch.repOK());
				} catch (java.lang.IllegalArgumentException e) {
					assertTrue(sch.repOK());
				}
					assertTrue(sch.repOK());
					sch = (Schedule)nextObject(ois);

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
	public void test_finishProcess() {
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			Schedule sch = (Schedule)nextObject(ois);
			while(sch != null){
				count++;
					
					sch.finishProcess();
					assertTrue(sch.repOK());
					sch = (Schedule)nextObject(ois);

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
	public void test_quantum() {
		
			FileInputStream fileTestUnit;
		  	ObjectInputStream ois;
			try {
				fileTestUnit= new FileInputStream(pathFile);
				ois = new ObjectInputStream(fileTestUnit);
				Schedule sch = (Schedule)nextObject(ois);
				while(sch != null){
					count++;
						
						sch.quantumExpire();
						assertTrue(sch.repOK());
						sch = (Schedule)nextObject(ois);

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
	public void test_unblockProcess() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			Schedule sch = (Schedule)nextObject(ois);
			while(sch != null){
				count++;
				int i = ThreadLocalRandom.current().nextInt(-2, literals + 1);

				try {
					sch.unblockProcess(i);

		        } catch (java.lang.IllegalArgumentException e) {
					assertTrue(sch.repOK());
		        }
				assertTrue(sch.repOK());
					sch = (Schedule)nextObject(ois);

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
	public void test_upgradeProcess_good() {
			FileInputStream fileTestUnit;
		  	ObjectInputStream ois;
			try {
				fileTestUnit= new FileInputStream(pathFile);
				ois = new ObjectInputStream(fileTestUnit);
				Schedule sch = (Schedule)nextObject(ois);
				while(sch != null){
					count++;
					int i = ThreadLocalRandom.current().nextInt(-2, literals + 1);
					int j = ThreadLocalRandom.current().nextInt(-2, literals + 1);

					try {
						sch.upgradeProcessPrio(i,j);
			        } catch (java.lang.IllegalArgumentException | java.lang.StackOverflowError e) {
						assertTrue(sch.repOK());
			        }
					assertTrue(sch.repOK());
						sch = (Schedule)nextObject(ois);

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
	public void test_upgradeProcess_nogood() {
		
		FileInputStream fileTestUnit;
	  	ObjectInputStream ois;
		try {
			fileTestUnit= new FileInputStream(pathFile);
			ois = new ObjectInputStream(fileTestUnit);
			Schedule sch = (Schedule)nextObject(ois);
			while(sch != null){
				count++;
				int i = ThreadLocalRandom.current().nextInt(-2, literals + 1);

				try {
					sch.upgradeProcessPrio(0,i);
		        } catch (java.lang.IllegalArgumentException | java.lang.StackOverflowError e) {
					assertTrue(sch.repOK());
		        }
				assertTrue(sch.repOK());
					sch = (Schedule)nextObject(ois);

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
