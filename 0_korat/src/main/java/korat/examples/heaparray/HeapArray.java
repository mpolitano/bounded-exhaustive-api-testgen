package korat.examples.heaparray;


import java.io.Serializable;

import korat.finitization.IArraySet;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.impl.FinitizationFactory;

/**
 * HeapArray: Heap array implementation took from Korat. 
 * Added builders:
 *     - HeapArray()
 *     - add(int i)
 */
public class HeapArray implements Serializable {


	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private int size;

    private int array[];

    private static final int MAX_SIZE = 10;
    
    /*
     * Builders ---------------------------
     */
    public HeapArray() {
        array = new int[MAX_SIZE];
        for (int i=0;i<MAX_SIZE;i++) {
            array[i] = -1;
        }
        size = 0;
    }
    
    public void add(int elem) {
        if (elem < 0)
            throw new IllegalArgumentException("The element must be a positive number");
        
        if (size<MAX_SIZE) {
            array[size] = elem;
            size++;
            
            bubbleUp();
        }
  
    }
    
    /**
     * Performs the "bubble up" operation to place a newly inserted element 
     * (i.e. the element that is at the size index) in its correct place so 
     * that the heap maintains the max-heap order property.
     */
    private void bubbleUp() {
        int index = this.size-1;
        
        while (hasParent(index)
                && (parent(index) < array[index])) {
            // parent/child are out of order; swap them
            swap(index, parentIndex(index));
            index = parentIndex(index);
        }        
    }
    
    private boolean hasParent(int i) {
        return i >= 1;
    }
    
    private int parent(int i) {
        return array[parentIndex(i)];
    }
    
    private int parentIndex(int i) {
        return (i - 1) / 2;
    }
    
    private void swap(int index1, int index2) {
        int tmp = array[index1];
        array[index1] = array[index2];
        array[index2] = tmp;        
    }
    /*
     * -----------------------------------------
     */

    public String toString() {
        String s = "";
        if (array != null) {
            for (int i = 0; i < array.length; i++) {
                s = s + array[i] + " ";
            }
            s += ", size = " + size + ", array.length = " + array.length;
        }
        return s;
    }
    
    public boolean repOK() {

        if (array == null)
            return false;

        if (size < 0 || size > array.length)
            return false;

        for (int i = 0; i < size; i++) {
            int elem_i = array[i];
            if (elem_i == -1)
                return false;

            if (i > 0) {
                int elem_parent = array[(i - 1) / 2];
                if (elem_i > elem_parent)
                    return false;
            }
        }

        for (int i = size; i < array.length; i++)
            if (array[i] != -1)
                return false;

        return true;

    }

    public static IFinitization finHeapArray(int n) {
        return finHeapArray(n, n, n);
    }
    
    public static IFinitization finHeapArray(int maxSize, int maxArrayLength,
            int maxArrayValue) {

        IFinitization f = FinitizationFactory.create(HeapArray.class);

        IIntSet sizes = f.createIntSet(0, 1, maxSize);

        IIntSet arrayLength = f.createIntSet(0, 1, maxArrayLength);
        IIntSet arrayValues = f.createIntSet(-1, 1, maxArrayValue);
        IArraySet arrays = f.createArraySet(int[].class, arrayLength, arrayValues, 1);

        f.set("size", sizes);
        f.set("array", arrays);

        return f;
    }

}
