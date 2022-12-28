package korat.examples.sortedlist;

import java.io.Serializable;
import java.util.Set;

import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

/**
 * SortedList: singly sorted linked list implementation took from Korat. 
 * Added builders:
 *     - SortedList()
 *     - add(int value)
 */
@SuppressWarnings("unchecked")
public class SortedList implements Serializable{
    
    /**
     * 
     */
    private static final long serialVersionUID = 1L;

   
    
    private Entry header;

    private int size = 0;

    /*
     * Builders -----------------------------------------
     */
    public SortedList(){
        header = new Entry();
        header.element = 0;
        header.next = header;
        header.previous = header;
        size = 0;
    }   

    public void add(int value){
        if (value>0) {
        Entry n = new Entry();
        n.element = value;
    
        Entry current = header.next;    
        Entry previous = header;
        
        if (size==0) {
            header.next = n;
            header.previous = n;
            n.previous = header;
            n.next = header;
        } else {
            int toVisit = size;
            while(current.element <= value && toVisit > 0){
                previous = current;     
                current = current.next;
                toVisit--;
            }
            n.next = current;
            if (current!=null)
                current.previous = n;
            previous.next = n;
            n.previous = previous;
        }
        size++;
        }
    }
    /*
     * -------------------------------------------------------
     */
    
    public boolean repOK() {
        // check cyclicity
        if (header == null)
            return false; 
        if (header.element != 0)
            return false;
        Set visited = new java.util.HashSet();
        visited.add(header);
        Entry current = header;
        while (true) {
            Entry next = current.next;
            if (next == null)
                return false;
            if (next!=header && next.element==0)
                return false;
            if (next.previous != current)
                return false;
            current = next;
            if (!visited.add(next))
                break;
        }
        if (current != header)
            return false; // maybe not needed
        
        // check size
        if (visited.size() - 1 != size)
            return false;
        
        // check ordering
        for (current = header.next; current.next != header; current = current.next) {
            if  (current.element==0 || current.next.element==0 || current.element > current.next.element)
                return false;
        }
        return true;
    }


    public static IFinitization finSortedList(int size){
        return finSortedList(0,size,size,size-1);
    }

    public static IFinitization finSortedList(int minSize, int maxSize,
            int numEntries, int numElems) {
        IFinitization f = FinitizationFactory.create(SortedList.class);

        IObjSet entries = f.createObjSet(Entry.class, true);
        entries.addClassDomain(f.createClassDomain(Entry.class, numEntries));
        IIntSet sizes = f.createIntSet(minSize, maxSize);

        /*IObjSet elems = f.createObjSet(Integer.class);
        IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
        elemsClassDomain.includeInIsomorphismCheck(false);
        for (int i = 1; i <= numElems; i++)
            elemsClassDomain.addObject(new Integer(i));
        elems.addClassDomain(elemsClassDomain);
        elems.setNullAllowed(true);*/
        IIntSet elems = f.createIntSet(0, numElems);

        f.set("header", entries);
        f.set("size", sizes);
        f.set(Entry.class, "element", elems);
        f.set(Entry.class, "next", entries);
        f.set(Entry.class, "previous", entries);
        return f;
    }

}