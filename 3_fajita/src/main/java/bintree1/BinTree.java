package bintree1;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;


import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

public class BinTree  implements java.io.Serializable{
    private Node root; // root node

    private int size = 0; // number of nodes in the tree

    private static final long serialVersionUID = 1L;

    /*************Builders******************/
    public void add(int x) {
        Node current = root;

        if (root == null) {
            {/*$goal 0 reachable*/}
            root = new Node();
            initNode(root,x);
            size++; //BUG: add by Mariano
            return;
        } 

        while (!current.info.equals(x)) {
            
            {/*$goal 1 reachable*/}
            
            if (x < current.info) {
                
                {/*$goal 2 reachable*/}
                
                if (current.left == null) {
                    {/*$goal 3 reachable*/}
                    current.left = new Node();
                    initNode(current.left,x);
                     size++; //BUG: add by Mariano
                } else {
                    {/*$goal 4 reachable*/}
                    current = current.left;
                }
            } else {
                {/*$goal 5 reachable*/}
                
                if (current.right == null) {
                    {/*$goal 6 reachable*/}
                    current.right = new Node();
                    initNode(current.right,x);
                    size++; //BUG: add by Mariano

                } else {
                    {/*$goal 7 reachable*/}
                    current = current.right;
                }
            }
        }
//      size++; //BUG: removed by Mariano
        {/*$goal 8 reachable*/}
    }

    private void initNode(Node root2, int x) {
        root2.info = x;
        root2.left = null;
        root2.right = null;
    }

    /*************From here BFS RepOK related routines******************/

    /**Breadh first seach KORAT_TUNNEADO
     * take from korat*/
    public boolean repOK() {
        // checks that empty tree has size zero
        if (root == null)
            return size == 0;
        // checks that the input is a tree
        if (!isAcyclic())
            return false;
        // checks that data is ordered
        if (!isOrdered(root))
            return false;
        // checks that size is consistent
        if (numNodes(root) != size)
            return false;

        return true;
    }

    private boolean isAcyclic() {
        Set<Node> visited = new HashSet<Node>();
        visited.add(root);
        LinkedList<Node> workList = new LinkedList<Node>();
        workList.add(root);
        while (!workList.isEmpty()) {
            Node current = (Node) workList.removeFirst();
            if (current.left != null) {
                // checks that the tree has no cycle
                if (!visited.add(current.left))
                    return false;
                workList.add(current.left);
            }
            if (current.right != null) {
                // checks that the tree has no cycle
                if (!visited.add(current.right))
                    return false;
                workList.add(current.right);
            }
        }
        return true;
    }

    private int numNodes(Node n) {
        if (n == null)
            return 0;
        return 1 + numNodes(n.left) + numNodes(n.right);
    }

    private boolean isOrdered(Node n) {
        return isOrdered(n, -1, -1);
    }

    private boolean isOrdered(Node n, int min, int max) {
        if (n.info == null)
            return false;
        //if (n.info == -1)
        //   return false;
        // if ((min != null && n.info.compareTo(min) <= 0)
        // || (max != null && n.info.compareTo(max) >= 0))
        if ((min != -1 && n.info <= (min)) || (max != -1 && n.info >= (max)))

            return false;
        if (n.left != null)
            if (!isOrdered(n.left, min, n.info))
                return false;
        if (n.right != null)
            if (!isOrdered(n.right, n.info, max))
                return false;
        return true;
    }


    /********************************************************/

    public String toString() {
        StringBuffer buf = new StringBuffer();
        buf.append("{");
        if (root != null)
            buf.append(root.toString());
        buf.append("}");
        return buf.toString();
    }



    public static IFinitization finBinTree(int size) throws Exception {

        IFinitization f = FinitizationFactory.create(BinTree.class);

        IObjSet nodes = f.createObjSet(Node.class,size);
        nodes.setNullAllowed(true);

        IIntSet sizes = f.createIntSet(0, size);

        IObjSet elems = f.createObjSet(Integer.class);
        IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
        elemsClassDomain.includeInIsomorphismCheck(false);
        for (int i = 0; i < size; i++)
            elemsClassDomain.addObject(new Integer(i));
        elems.addClassDomain(elemsClassDomain);
//      elems.setNullAllowed(false); //not null allowed

        f.set("root", nodes);
        f.set("size", sizes);
        f.set("Node.left", nodes);
        f.set("Node.right", nodes);
        f.set("Node.info", elems);

        return f;

    }

}
