package korat.examples.singlylinkedlist;

import java.io.Serializable;

public class Entry implements Serializable {

    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	Object element;

    Entry next;

    public Entry(Object elem,Entry n) {
    	element = elem;
    	next = n;
    }
    
    public String toString() {
        return "[" + (element != null ? element.toString() : "null") + "]";
    }

}
