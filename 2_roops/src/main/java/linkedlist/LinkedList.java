//$category roops.core.objects

//Authors: Marcelo Frias
//$benchmarkclass
/**
 * @Invariant 
 *		( this.header!=null ) &&
 *		( this.header.next!=null ) &&
 *		( this.header.previous!=null ) &&
 *		( this.size==#(this.header.*next @- null)-1 ) &&
 *		( this.size>=0 ) &&
 *		(all n: LinkedListNode | ( n in this.header.*next @- null ) => (
 *				  n!=null &&
 *				  n.previous!=null &&
 *				  n.previous.next==n &&
 *				  n.next!=null &&
 *				  n.next.previous==n )) ; 
 *
 */
package linkedlist;
import java.util.Set;

import korat.finitization.IClassDomain;
import korat.finitization.IFieldDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;


import java.util.HashSet;
public class LinkedList  implements java.io.Serializable{
    
    private static final long serialVersionUID = 1L;

	
	//$goals 3
	//$benchmark
	public void addLastTest(LinkedList list, Object o) {
		if (list!=null && list.repOK()) {
		  boolean ret_val = list.addLast(o);
		}
	}

	//$goals 3
	//$benchmark
	public void containsTest(LinkedList list, Object arg) {
		if (list!=null && list.repOK()) {
		  boolean ret_val = list.contains(arg);
		}
	}

	//$goals 10
	//$benchmark
	public void removeIndexTest(LinkedList list, int index) {
		if (list!=null && list.repOK()) {
		  Object ret_val = list.removeIndex(index);
		}
	}


	public /*@ nullable @*/LinkedListNode header;
	
	public int size;
	
	public int modCount;

	private void init() {
		header = createHeaderNode();
	}


	//-----------------------------------------------------------------------
	private int indexOf(Object new_value) {
		int i = 0;
		for (LinkedListNode node = header.next; node != header; node = node.next) {
			{/*$goal 0 reachable*/}
			if (isEqualValue(node.value, new_value)) {
				{/*$goal 1 reachable*/}
				return i;
			}
			i++;
		}
		{/*$goal 2 reachable*/}
		return -1;
	}

	
	public boolean contains(Object arg) {
		return indexOf(arg) != -1;
	}

	
	public Object removeIndex(int index) {
		LinkedListNode node = getNode(index, false);
		Object oldValue = node.value;
		removeNode(node);
		
		{/*$goal 9 reachable*/}
		return oldValue;
	}

	
	public boolean addLast(Object o) {
		addNodeBefore(header, o);
		return true;
	}

	private boolean isEqualValue(Object value1, Object value2) {
		boolean ret_val;
		if (value1 == value2) {
			ret_val=true;
		} else {
			if (value1==null) {
				ret_val = false;
			} else {
				ret_val = value1.equals(value2);
			}
		}
		return ret_val;
	}

	private LinkedListNode createHeaderNode() {
		LinkedListNode linkedListNode = new LinkedListNode();
		linkedListNode.next = linkedListNode;
		linkedListNode.previous = linkedListNode;
		return linkedListNode;
	}


	private LinkedListNode createNode(Object new_object_value) {
		{/*$goal 0 reachable*/}
		LinkedListNode node = new LinkedListNode();
		node.previous = node;
		node.next = node;
		node.value = new_object_value;
		return node;
	}

	

	private void addNodeBefore(LinkedListNode node, Object new_object_value) {
		LinkedListNode newNode = createNode(new_object_value);
		{/*$goal 1 reachable*/}
		
		addNode(newNode, node);
	}

	private void addNode(LinkedListNode nodeToInsert,
			LinkedListNode insertBeforeNode) {
		nodeToInsert.next = insertBeforeNode;
		nodeToInsert.previous = insertBeforeNode.previous;
		insertBeforeNode.previous.next = nodeToInsert;
		insertBeforeNode.previous = nodeToInsert;
		size++;
		modCount++;
		
		{/*$goal 2 reachable*/}
	}


	private void removeNode(LinkedListNode node) {
		node.previous.next = node.next;
		node.next.previous = node.previous;
		size--;
		modCount++;
		{/*$goal 8 reachable*/}
	}


	private LinkedListNode getNode(int index, boolean endMarkerAllowed)
			 {
		// Check the index is within the bounds
		if (index < 0) {
			{/*$goal 0 reachable*/}
			throw new RuntimeException();
		}
		if (!endMarkerAllowed && index == size) {
			{/*$goal 1 reachable*/}
			throw new RuntimeException();
		}
		if (index > size) {
			{/*$goal 2 reachable*/}
			throw new RuntimeException();
		}
		// Search the list and get the node
		LinkedListNode node;
		int size_div_2 = size /2;
		
		if (index < size_div_2) {
			{/*$goal 3 reachable*/}
			// Search forwards
			node = header.next;
			for (int currentIndex = 0; currentIndex < index; currentIndex++) {
				{/*$goal 4 reachable*/}
				node = node.next;
			}
		} else {
			
			{/*$goal 5 reachable*/}
			
			// Search backwards
			node = header;
			for (int currentIndex = size; currentIndex > index; currentIndex--) {
				{/*$goal 6 reachable*/}
				node = node.previous;
			}
		}
		{/*$goal 7 reachable*/}
		return node;
	}

        public LinkedList() {
           init();
        }

        public static IFinitization finLinkedList(int numEntries) {
        
            IFinitization f = FinitizationFactory.create(LinkedList.class);
            
            IObjSet entries = f.createObjSet(LinkedListNode.class,numEntries);
            entries.setNullAllowed(true);
            entries.addClassDomain(f.createClassDomain(LinkedListNode.class, numEntries));
            
            IObjSet elems = f.createObjSet(Integer.class);
            IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
            elemsClassDomain.includeInIsomorphismCheck(false);
            for (int i = 0; i < numEntries; i++)
                elemsClassDomain.addObject(new Integer(i));
            elems.addClassDomain(elemsClassDomain);
            elems.setNullAllowed(true);
            
             
            IIntSet sizes = f.createIntSet(0, numEntries);
            
            f.set("header", entries);
            f.set("size", sizes);
                        
            f.set("LinkedListNode.value", elems);
            f.set("LinkedListNode.next", entries);
            f.set("LinkedListNode.previous", entries);
        
        
            return f;

        }
	//*************************************************************************
	//************** From now on repOK()  *************************************
	//*************************************************************************

        public boolean repOK()
        {
            if (header == null)
                return false;
            if (header.value != null)
                return false;

            Set visited = new HashSet();
            visited.add(header);
            LinkedListNode current = header;

            while (true)
            {
                LinkedListNode next = current.next;
                if (next == null)
                    return false;
                if (next.previous != current)
                    return false;
                //Add by Mariano.
                if(current.value == null && current != header)
                    return false;
                //---
                current = next;
                if (!visited.add(next))
                    break;
            }
            if (current != header)
                return false;

            if (visited.size() - 1 != size)
                return false;

            return true;
        }



}
//$endcategory roops.core.objects
