package korat.examples.singlylinkedlist;

import java.io.Serializable;

public class SerializableObject implements Serializable {

    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	static int objectID = 0;

    private static int myID;

    public SerializableObject() {
        myID = objectID++;
    }

    public String toString() {
        return "#" + myID;
    }

    public int getValue() {
    	return myID;
    }
    
}