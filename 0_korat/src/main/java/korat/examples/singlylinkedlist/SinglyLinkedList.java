package korat.examples.singlylinkedlist;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

// import korat.finitization.IClassDomain;
// import korat.finitization.IFinitization;
// import korat.finitization.IIntSet;
// import korat.finitization.IObjSet;
// import korat.finitization.impl.FinitizationFactory;

/**
 * SinglyLinkedList: singly linked list implementation took from Korat. 
 * Added builders:
 *     - SinglyLinkedList()
 *     - add(Element element)
 *     
 */
public class SinglyLinkedList implements Serializable {

	
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public Entry header;

    private int size = 0;

    /*
     * Builders ---------------------------
     */
    public SinglyLinkedList(){
        header = new Entry(null,null);
        size = 0;
    }

    public void add(Object element) {
        if (element==null)
            throw new IllegalArgumentException();

        Entry current = header.next;
        Entry previous = header;

        while(current!=null){
            previous = current;     
            current = current.next;
        }
        
        Entry n = new Entry(element,current);
        previous.next = n;
        size++;
    }
    /*
     * -----------------------------------------
     */

    public boolean repOK() {
    	return repOkNS();
    }
    
    public boolean repOkCommon() {
        if (header == null)
            return false;

        if (header.element != null)
            return false;

        Set<Entry> visited = new java.util.HashSet<Entry>();
        visited.add(header);
        Entry current = header;

        while (true) {
            Entry next = current.next;
            if (next == null)
                break;

            if (next.element == null)
                return false;

            if (!visited.add(next))
                return false;

            current = next;
        }

        // if (current != header)
        // return false; // // maybe not needed (also in SortedList.java)

        if (visited.size() - 1 != size)
            return false;

        return true;
    }

    public boolean repOkNS() {
        if (!repOkCommon())
            return false;
        return true;
    }

    @SuppressWarnings("unchecked")
    public boolean repOkSorted() {
        if (!repOkCommon())
            return false;

        // check for sorted
        if ((header.next != header)
                && (!(header.next.element instanceof Comparable)))
            return false;

        for (Entry current = header.next; current.next != header; current = current.next) {
            if ((!(current.next.element instanceof Comparable))
                    || (((Comparable) current.element).compareTo((Comparable) current.next.element) > 0))
                return false;
        }
        return true;
    }

    public String toString() {
        String res = "(";
        if (header != null) {
            Entry cur = header.next;
            while (cur != null && cur != header) {
                res += cur.toString();
                cur = cur.next;
            }
        }
        return res + ")";
    }
    
    // public static IFinitization finSinglyLinkedList(int size) {
    //     return finSinglyLinkedList(size, size, size, size);
    // }
            
    // public static IFinitization finSinglyLinkedList(int minSize, int maxSize,
    //         int numEntries, int numElems) {

    //     IFinitization f = FinitizationFactory.create(SinglyLinkedList.class);

    //     IObjSet entries = f.createObjSet(Entry.class);
    //     entries.setNullAllowed(true);
    //     entries.addClassDomain(f.createClassDomain(Entry.class, numEntries));

    //     IObjSet elems = f.createObjSet(Integer.class);
    //     IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
    //     elemsClassDomain.includeInIsomorphismCheck(false);
    //     for (int i = 0; i < numElems; i++)
    //         elemsClassDomain.addObject(new Integer(i));
    //     elems.addClassDomain(elemsClassDomain);
    //     elems.setNullAllowed(true);

    //     IIntSet sizes = f.createIntSet(0, maxSize);

    //     f.set("header", entries);
    //     f.set("size", sizes);
    //     f.set("Entry.element", elems);
    //     f.set("Entry.next", entries);

    //     return f;

    // }

}
