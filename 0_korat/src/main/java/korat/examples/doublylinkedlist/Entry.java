package korat.examples.doublylinkedlist;

import java.io.Serializable;

public class Entry implements Serializable {

	
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	Object element;

    Entry next;

    Entry previous;

    public String toString() {
        return "[" + (element != null ? element.toString() : "null") + "]";
    }

}
