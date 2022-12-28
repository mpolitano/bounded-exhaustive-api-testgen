package korat.examples.linkedlist;

import java.io.Serializable;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;
import java.util.HashSet;

public class LinkedList implements Serializable{
    
    /**
     * 
     */
    private static final long serialVersionUID = 1L;
	//singly linked list

	public static class Node implements Serializable {
        /**
         * 
         */
        private static final long serialVersionUID = 1L;

		Node next;
		int data;

		public Node(int data){
			this.data=data;
		}
	}

	private Node head;
	private int size;
	
	 /*
     * Builders ---------------------------
     */
    public LinkedList() {
    }

	public Node add(int data) {
		Node newEntry = new Node(data);
	    newEntry.next = head;
	    head = newEntry;
	    size++;
	    return newEntry;
	}

	public boolean repOK() {
		if (head == null)
			return size == 0;
		int count = 0;
		
		//Check how many elements are in the linkedlist 
		Node root = head;
		HashSet<Node> nodes = new HashSet<Node>();
		while (root != null) {
			if (nodes.contains(root)) return false;
			nodes.add(root);
			root = root.next;
			count++;
		}
		return count == size;
	}
	public static IFinitization finLinkedList(int size) {
		return finLinkedList(size,0,size,size-1);
	} 


	public static IFinitization finLinkedList(int nodesNum, int minSize, int maxSize, 
			int maxVal) {
		 IFinitization f = FinitizationFactory.create(LinkedList.class);
		 IObjSet nodes = f.createObjSet(Node.class, nodesNum, true);
		 f.set("head", nodes);
		 f.set("Node.next", nodes);
		 IIntSet values = f.createIntSet(0, maxVal);
		 f.set("Node.data", values);
		 IIntSet sizes = f.createIntSet(minSize, maxSize);
		 f.set("size", sizes);
		 return f;
	}
}