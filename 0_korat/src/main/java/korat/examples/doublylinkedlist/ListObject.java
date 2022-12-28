package korat.examples.doublylinkedlist;

import java.io.Serializable;

public class ListObject implements Serializable {

	
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	static int objectID = 0;

    private static int myID;

    public ListObject() {
        myID = objectID++;
    }

    public String toString() {
        return "#" + myID;
    }
}