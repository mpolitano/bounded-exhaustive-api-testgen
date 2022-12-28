package korat.examples.doublylinkedlist;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

public class DoublyLinkedList implements Serializable {

	
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public Entry header;

    private int size = 0;
    
    /*
     * Builders ---------------------------
     */
    public DoublyLinkedList() {
        header = new Entry();
        header.element = null;
        header.next = header;
        header.previous = header;
        size = 0;
    }
    
    public void add(Object obj) {
        if (obj==null)
            throw new IllegalArgumentException();
        
        if (header.element ==null) {
            header.element = obj;
        } else {
            Entry n = new Entry();
            n.element = obj;
            n.next = header;
            n.previous = header.previous;
            header.previous.next = n;
            header.previous = n;
        }
        
        size++;
    }
    /*
     * -----------------------------------------
     */

    public boolean repOK() {
        return repOkNS();
    }
    
    @SuppressWarnings("unchecked")
    public boolean repOkCommon() {

        if (header == null)
            return false;
        if (header.element == null)
            return size == 0 && header.next == header
                    && header.previous == header;

        Set visited = new java.util.HashSet();
        visited.add(header);
        Entry current = header;

        while (true) {
            Entry next = current.next;
            if (next == null)
                return false;
            if (next.previous != current)
                return false;
            if (current.element==null)
            	return false;
            current = next;
            if (!visited.add(next))
                break;
        }
        if (current != header)
            return false; // // maybe not needed (also in SortedList.java)
        if (visited.size() != size)
            return false;
        return true;
    }
    
    public boolean repOkNS() {
        return repOkCommon();
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
        String res = "";
        Entry cur = this.header;
        while (cur != null) {
            res += cur.toString();
            cur = cur.next;
            if (cur == header)
                break;
        }
        return res;
    }

    public static IFinitization finDoublyLinkedList(int size) {
        return finDoublyLinkedList(0, size, size);
    }
        
    public static IFinitization finDoublyLinkedList(int minSize, int maxSize,
            int numEntries) {
        
        IFinitization f = FinitizationFactory.create(DoublyLinkedList.class);

        IObjSet entries = f.createObjSet(Entry.class, true);
        entries.addClassDomain(f.createClassDomain(Entry.class, numEntries));

        IObjSet elems = f.createObjSet(Integer.class);
        IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
        elemsClassDomain.includeInIsomorphismCheck(false);
        for (int i = 0; i < numEntries; i++)
            elemsClassDomain.addObject(new Integer(i));
        elems.addClassDomain(elemsClassDomain);
        elems.setNullAllowed(true);

                    
        IIntSet sizes = f.createIntSet(minSize, maxSize);

        f.set("header", entries);
        f.set("size", sizes);
        f.set(Entry.class, "element", elems);
        f.set(Entry.class, "next", entries);
        f.set(Entry.class, "previous", entries);
        
        return f;
        
    }

}
