package util;

import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.util.Collection;
import java.util.LinkedList;

public class Deserializer {

        private static ObjectInputStream ois;	

	public static Collection<Object> deserialize(String file) throws IOException{		
		FileInputStream fileTestUnit = new FileInputStream(new File(file));
		ois= new ObjectInputStream(fileTestUnit);
		Collection<Object> res = new LinkedList<Object>();
		try{
			Object obj = nextObject(); 
			while(obj != null){
				res.add(obj); 
				obj = nextObject();
			}
			ois.close();
		}catch (Exception e) {
			e.printStackTrace();
		}
		return res;
	}

        private static Object nextObject() throws ClassNotFoundException, IOException {
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
