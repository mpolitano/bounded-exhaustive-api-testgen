package list;

import java.util.Set;

import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;
import java.io.Serializable;

/**
 * @Invariant all n: SinglyLinkedListNode | ( ( n in this.header.*next @- null ) => ( n !in n.next.*next @- null ) ) ;
 */
/**
 * @SpecField myseq: seq SinglyLinkedListNode from this.header, SinglyLinkedListNode.next | (
 *		( #(this.header.*next @- null) = #(this.myseq) ) && 
 *		( this.header=null => #(this.myseq)=0 ) && 
 *		( this.header!= null => this.header=this.myseq[0] ) && 
 *		( all i: int | ( ( i >= 0 && i < ( #(this.myseq) - 1) ) => ( this.myseq[i + 1] = this.myseq[i].next ) ) )
 *		) ;
 */
public class SinglyLinkedList implements Serializable{
    
    /**
     * 
     */
    private static final long serialVersionUID = 1L;

	/*@ nullable @*/SinglyLinkedListNode header;
	
	public SinglyLinkedList(){
		header = new SinglyLinkedListNode();
		header.value = null;
	}
	

	/**
	 * @Modifies_Everything
	 * 
	 * @Ensures (some i: int | ( ( i>=0 && i < #(this.myseq) ) && (this.myseq[i] in SinglyLinkedListNode) && (this.myseq[i].value=value_param)) ) <=> return=true ;
	 */
	public boolean contains(/*@ nullable @*/Object value_param) {
		SinglyLinkedListNode current;
		boolean result;

		current = this.header;
		result = false;
		while (result == false && current != null) {
			boolean equalVal;

			// begin equalVal = this.jml_isEqualValue(current.nodeValue,
			// value_param);
			if (value_param == null && current.value == null)
				equalVal = true;
			else if (value_param != null)

				if (value_param == current.value)
					equalVal = true;
				else
					equalVal = false;
			else
				equalVal = false;
			// end equalVal = this.jml_isEqualValue(current.nodeValue,
			// value_param);

			if (equalVal == true) {
				result = true;
			}
			current = current.next;
		}
		return result;
	}

	/**
	 * @Requires ( index>=0 && index<#(this.myseq) ) ;
	 * 
	 * @Modifies_Everything
	 *
	 * @Ensures ( #(this.myseq) = #(@old(this.myseq))-1 ) && 
	 *		( all i: int | ( (i>=0 && i<index ) => (this.myseq[i] = @old(this.myseq[i]) ) )) && 
	 *		( all j: int | ( (j>=index && j<#(this.myseq)) => this.myseq[j]=@old(this.myseq[j+1]) ) ) ;
	 */
	public void remove(int index) {
		SinglyLinkedListNode current;
		// current = this.header;
		current = this.header.next;

		SinglyLinkedListNode previous;
		// previous = null;
		previous = this.header;
		int current_index;
		current_index = 0;
		
		boolean found = false;
		
		while (found==false && current != null) {
			if (index == current_index) {
				found = true;
			} else {
				current_index = current_index + 1;
				previous = current;
				current = current.next;
			}
		}
		
		if (previous == this.header)
			this.header.next = null;
		else
			previous.next = current.next;
		
	}

	/**
	 * @Modifies_Everything
	 * 
	 * @Ensures ( #(this.myseq)=#(@old(this.myseq))+1 ) && 
	 *          ( this.myseq[#(this.myseq)-1].value=arg ) && 
	 *		    ( all i: int | ( ( i>=0 && i<#(@old(this.myseq)) ) => ( this.myseq[i]=@old(this.myseq[i]) )) )
	 */
	public void insertBack(/*@ nullable @*/Integer arg) {
		SinglyLinkedListNode freshNode = new SinglyLinkedListNode();
		freshNode.value = arg;
		freshNode.next = null;

		//Bug, repOK say that header == null
		// if (this.header == null)
		// 	this.header = freshNode;
		// else {

			SinglyLinkedListNode current;
			current = this.header;
			while (current.next != null) {
				current = current.next;
			}
			current.next = freshNode;
		// }
	}
	
		
    public boolean repOK2() {
        return repOkNS();
    }

    public boolean repOkCommon() {
        if (header == null)
            return false;
        if (header.value != null)
            return false;
        Set<SinglyLinkedListNode> visited = new java.util.HashSet<SinglyLinkedListNode>();
        visited.add(header);
        SinglyLinkedListNode current = header;
        while (true) {
            SinglyLinkedListNode next = current.next;
            if (next == null)
                break;
            if (next.value == null)
                return false;
            if (!visited.add(next))
                return false;
            current = next;
        }

        return true;
    }
    
    
    public boolean repOK() {
        if (header == null)
            return false;
        if (header.value != null)
            return false;
        Set<SinglyLinkedListNode> visited = new java.util.HashSet<SinglyLinkedListNode>();
        visited.add(header);
        SinglyLinkedListNode current = header;
        while (true) {
            SinglyLinkedListNode next = current.next;
            if (next == null)
                break;
            if (!visited.add(next))
                return false;
            current = next;
        }
        current = header;
        while (true) {
            SinglyLinkedListNode next = current.next;
            if (next == null)
                break;
            if (next.value == null)
                return false;
            current = next;
        }	
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
                && (!(header.next.value instanceof Comparable)))
            return false;

        for (SinglyLinkedListNode current = header.next; current.next != header; current = current.next) {
            if ((!(current.next.value instanceof Comparable))
                    || (((Comparable) current.value).compareTo((Comparable) current.next.value) > 0))
                return false;
        }
        return true;
    }

  	

	public static IFinitization finSinglyLinkedList(int size) {

		return finSinglyLinkedList(size,0,size,size-1);
	}

	public static IFinitization finSinglyLinkedList(int numEntries, int minSize, int maxSize,
            int numElems) {

        IFinitization f = FinitizationFactory.create(SinglyLinkedList.class);

        IObjSet entries = f.createObjSet(SinglyLinkedListNode.class);
        entries.setNullAllowed(true);
        entries.addClassDomain(f.createClassDomain(SinglyLinkedListNode.class, numEntries));

        IObjSet elems = f.createObjSet(Integer.class);
		IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
		elemsClassDomain.includeInIsomorphismCheck(false);


		for (int i =0; i <= numElems; i++)
			elemsClassDomain.addObject(new Integer(i));
		elems.addClassDomain(elemsClassDomain);
		elems.setNullAllowed(true);


        f.set("header", entries);
        f.set("SinglyLinkedListNode.value", elems);
        f.set("SinglyLinkedListNode.next", entries);

        return f;

    }
	
	/*public static void main(String[] args) {
		SinglyLinkedList list = new SinglyLinkedList();
		list.insertBack(new Object());
		list.remove(0);
		
	}*/
	
	
	
}
