package singlelist;
//$category roops.core.objects

import java.util.HashSet;
import java.util.Set;

import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

//Authors: Marcelo Frias
//$benchmarkclass
/**
 * @Invariant all n: SinglyLinkedListNode | ( ( n in this.header.*next @- null ) => ( n !in n.next.*next @- null ) ) ;
 */
public class SinglyLinkedList  implements java.io.Serializable{

    private static final long serialVersionUID = 1L;

	//$goals 7
	//$benchmark
//	public void containsTest(roops.core.objects.SinglyLinkedList list, Object value_param) {
//		boolean ret_val;
//		if (list!=null && list.repOK()) {
//		  ret_val = list.contains(value_param);
//		}
//	}

	//$goals 4
	//$benchmark
	public void insertBackTest(SinglyLinkedList list, Object arg) {
		if (list!=null && list.repOK()) {
		  list.insertBack(arg);
		}
	}

	//$goals 7
	//$benchmark
	public void removeTest(SinglyLinkedList list, int index) {
		if (list!=null && list.repOK()) {
		  list.remove(index);
		}
	}

	
	public /*@ nullable @*/SinglyLinkedListNode header;


	
	public boolean contains(Object value_param) {
		SinglyLinkedListNode current;
		boolean result;

		current = this.header;
		result = false;
		while (result == false && current != null) {
			{/*$goal 0 reachable*/}
			
			boolean equalVal;

			if (value_param == null && current.value == null){
				{/*$goal 1 reachable*/}
				equalVal = true;
			} else if (value_param != null) {

				if (value_param == current.value) { 
					{/*$goal 2 reachable*/}
					equalVal = true;
				} else {
					{/*$goal 3 reachable*/}
					equalVal = false;
				}
			} else {
				{/*$goal 4 reachable*/}
				equalVal = false;
			}

			if (equalVal == true) {
				{/*$goal 5 reachable*/}
				result = true;
			}
			current = current.next;
		}
		{/*$goal 6 reachable*/}
		return result;
	}

	


	
	public void remove(int index) {
		
		if (index<0) {
			{/*$goal 0 reachable*/}
			throw new RuntimeException();
		}
		
		SinglyLinkedListNode current;
		current = this.header;
		SinglyLinkedListNode previous;
		previous = null;
		int current_index;
		current_index = 0;
		
		boolean found = false;
		
		while (found==false && current != null) {
			{/*$goal 1 reachable*/}
			
			if (index == current_index) {
				{/*$goal 2 reachable*/}
				found = true;
			} else {
				{/*$goal 3 reachable*/}
				current_index = current_index + 1;
				previous = current;
				current = current.next;
			}
		}
		
		if (found==false) {
			{/*$goal 4 reachable*/}			
			throw new RuntimeException();
		}
		
		if (previous == null){
			{/*$goal 5 reachable*/}			
			this.header = current.next;
	    } else {
	    	{/*$goal 6 reachable*/}
			previous.next = current.next;
	    }
	}

	

	public void insertBack(Object arg) {
		SinglyLinkedListNode freshNode = new SinglyLinkedListNode();
		freshNode.value = arg;
		freshNode.next = null;

		if (this.header == null) {
			{/*$goal 0 reachable*/}
			this.header = freshNode;
		} else {
			{/*$goal 1 reachable*/}
			SinglyLinkedListNode current;
			current = this.header;
			while (current.next != null) {
				{/*$goal 2 reachable*/}
				current = current.next;
			}
			current.next = freshNode;
		}
		{/*$goal 3 reachable*/}
	}
	
	public SinglyLinkedList() {}

        //*************************************************************************
        //************** From now on repOK()  *************************************
        //*************************************************************************

        public boolean repOK() {

            Set visited = new HashSet();

            SinglyLinkedListNode current = header;

            while (true)
            {
                SinglyLinkedListNode next = current;
                if (next == null)
                    break;

                if (!visited.add(next))
                    return false;

                current = current.next;
            }

            return true;
        }
        
        public static IFinitization finSinglyLinkedList(int numEntries) {
            
            IFinitization f = FinitizationFactory.create(SinglyLinkedList.class);
            
            IObjSet entries = f.createObjSet(SinglyLinkedListNode.class,numEntries);
            entries.setNullAllowed(true);
            entries.addClassDomain(f.createClassDomain(SinglyLinkedListNode.class, numEntries));
            
            IObjSet elems = f.createObjSet(Integer.class);
            IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
            elemsClassDomain.includeInIsomorphismCheck(false);
            for (int i = 0; i < numEntries; i++)
                elemsClassDomain.addObject(new Integer(i));
            elems.addClassDomain(elemsClassDomain);
            elems.setNullAllowed(false);
                        
            f.set("header", entries);
                        
            f.set("SinglyLinkedListNode.value", elems);
            f.set("SinglyLinkedListNode.next", entries);
        
        
            return f;

        }

}
//$endcategory roops.core.objects
