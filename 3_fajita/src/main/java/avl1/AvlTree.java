package avl1;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;


import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;
import korat.finitization.IClassDomain;

//Authors: Marcelo Frias

/**
 * @Invariant all x: AvlNode | x in this.root.*(left @+ right) @- null => 
 * (
 *      (x !in x.^(left @+ right)) && 
 *      (all y: AvlNode | (y in x.left.*(left @+ right) @-null) => y.element < x.element ) && 
 *      (all y: AvlNode | (y in x.right.*(left @+right) @- null) => x.element < y.element ) && 
 *      (x.left=null && x.right=null => 
 *              x.height=0) && 
 *      (x.left=null && x.right!=null => 
 *              x.height=1 && x.right.height=0) && 
 *      (x.left!=null && x.right=null => 
 *              x.height=1 && x.left.height=0) && 
 *      (x.left!=null && x.right!=null => 
 *              x.height= (x.left.height>x.right.height ? 
 *      x.left.height : x.right.height )+1 && ( 
 *      (x.left.height > x.right.height ? 
 *      x.left.height - x.right.height : 
 *      x.right.height - x.left.height ))<=1));
 */
public class AvlTree implements java.io.Serializable{

    public  AvlNode root;
    public int size;
    
    //******************************************************
    //***** From now on functions for checking the repOk ***
    //******************************************************
    

    
    /***Breadth first KORAT-TUNNEADO*/
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
        if(!isBalanced())
            return false;
        return true;
    }
    
    private boolean isBalanced(){
        LinkedList<AvlNode> queue = new LinkedList<AvlNode>();
        queue.add(root);
        while (!queue.isEmpty()) {
            AvlNode current = (AvlNode) queue.removeFirst();
            int l_Height = current.left == null ? -1 : current.left.height;
            int r_Height = current.right == null ? -1 : current.right.height;
            int difference = l_Height - r_Height;
            if (difference < -1 || difference > 1)
                return false; // Not balanced.
            int max = l_Height > r_Height ? l_Height : r_Height;
            if (current.height != 1 + max)
                return false; // Wrong height.
            if (current.left != null) {
                queue.add(current.left);
            }
            if (current.right != null) {
                queue.add(current.right);
            }
        }
        return true;

        
    }
        
    private boolean isAcyclic() {
          Set<AvlNode> visited = new HashSet<AvlNode>();
          visited.add(root);
          LinkedList<AvlNode> workList = new LinkedList<AvlNode>();
          workList.add(root);
          while (!workList.isEmpty()) {
              AvlNode current = (AvlNode) workList.removeFirst();
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

        /***breadth first search NO TUNNEADO.
         * Take from fajita (Marcelo Frias): */
        public boolean repOKBFSNoTunning() { 
                HashSet<AvlNode> allNodes = new HashSet<AvlNode>();
                LinkedList<AvlNode> listallNodes = new LinkedList<AvlNode>();
                LinkedList<AvlNode> queue = new LinkedList<AvlNode>();
                if (root != null)
                   queue.add(root);
                while (!queue.isEmpty()) {
                    AvlNode node = queue.removeFirst();
                        if (!allNodes.add(node))
                            return false; // Not acyclic.
                        listallNodes.add(node);
                        if (node.left != null)
                            queue.addLast(node.left);
                        if (node.right != null)
                            queue.addLast(node.right);
                }
                if (!isOrdered(root))
                    return false;
                for (AvlNode node : listallNodes) {
                        int l_Height = node.left == null ? 0 : node.left.height;
                        int r_Height = node.right == null ? 0 : node.right.height;
                        int difference = l_Height - r_Height;
                        if (difference < -1 || difference > 1)
                            return false; // Not balanced.
                        int max = l_Height > r_Height ? l_Height : r_Height;
                        if (node.height != 1 + max)
                            return false; // Wrong height.
                }
                if (listallNodes.size() != size)
                    return false; // Wrong size.
                return true;
        }
        
        
        
        /***************************************************/
        
        /***breadth first search NO TUNNEADO.
         * Take from fajita (Marcelo Frias): 
         * Change from Deph First Search to breadth First Search */
    /**Trate de seguir la especificacion JML: Korat gana con este (o sea es el mas tunneado de todos
     *).*/
    public boolean repOKBFSNoTunning2() { 
            HashSet<AvlNode> allNodes = new HashSet<AvlNode>();
            LinkedList<AvlNode> queue = new LinkedList<AvlNode>();
            if (root != null)
               queue.add(root);
            while (!queue.isEmpty()) {
                AvlNode node = queue.removeFirst();
                if (!allNodes.add(node))
                    return false; // Not acyclic.
                if(!isOrdered(node)){
                    return false;
                }
               if(node.left==null && node.right==null){
                    if(node.height!=0){
                        return false;
                    }
                } 
                if(node.left==null && node.right!=null){
                    if(!(node.height==1 && node.right.height==0)){
                        return false;
                    }
                }
                if(node.left!=null && node.right==null){
                    if(!(node.height==1 && node.left.height==0)){
                        return false;
                    }
                }
                if(node.left!=null && node.right!=null){
                    int h = (node.left.height>node.right.height ? 
                            node.left.height : node.right.height )+1;
                    int h1 = (node.left.height > node.right.height ? 
                         node.left.height - node.right.height: 
                         node.right.height - node.left.height);
                    if(!((node.height== h) &&  h1 <=1)){
                        return false;
                    }
                }
                
                if (node.left != null)
                    queue.addLast(node.left);
                if (node.right != null)
                    queue.addLast(node.right);
            }
            if (allNodes.size() != size)
                return false; // Wrong size.
            return true;
    }

                    
       private int numNodes(AvlNode n) {
            if (n == null)
                return 0;
            return 1 + numNodes(n.left) + numNodes(n.right);
        }


        

//  private boolean isOrdered(AvlNode n) {
//      return n == null || isOrdered(n, null, null);
//  }

    //private boolean isOrdered(AvlNode n, Data min, Data max) {
//  private boolean isOrdered(AvlNode n, Integer min, Integer max) {    
//      if (n.data == null)
//          return false;
//
//      if ((min != null && n.data.compareTo(min)<=0)/*n.data<min*/ ||
//              (max != null && n.data.compareTo(max)>=0/*n.data >max*/))
//          return false;
//
//      /*if ((min != null && n.data.data_lt(min)) ||
//          (max != null && n.data.data_gt(max)))
//            return false;*/
//      if (n.left != null)
//          if (!isOrdered(n.left, min, n.data))
//              return false;
//      if (n.right != null)
//          if (!isOrdered(n.right, n.data, max))
//              return false;
//      return true;
//  }
    

     private boolean isOrdered(AvlNode n) {
         return isOrdered(n, -1, -1);
     }

     private boolean isOrdered(AvlNode n, int min, int max) {
         // if (n.info == null)
         // return false;
         if (n.data == -1)
             return false;
         // if ((min != null && n.info.compareTo(min) <= 0)
         // || (max != null && n.info.compareTo(max) >= 0))
         if ((min != -1 && n.data <= (min)) || (max != -1 && n.data >= (max)))

             return false;
         if (n.left != null)
             if (!isOrdered(n.left, min, n.data))
                 return false;
         if (n.right != null)
             if (!isOrdered(n.right, n.data, max))
                 return false;
         return true;
     }

    public static IFinitization finAvlTree(int maxSize) {
        return finAvlTree(maxSize, maxSize, 0, maxSize -1);
    }
    
    
    
    /**To generate AvlTrees that have a given number of nodes, the Korat
    search algorithm uses the ﬁnitization method.
    In this method we specify bounds on th number of objects to be used to 
    construct instances of the data structure, as well as possible values 
    stored in the ﬁelds of those objects.
     */
//     public static IFinitization finAvlTree(int numAvlNode, int minSize,
//             int maxSize,int numData){

//         IFinitization f = FinitizationFactory.create(AvlTree.class);

//         IObjSet entry = f.createObjSet(AvlNode.class,numAvlNode);
//         entry.setNullAllowed(true);
//         IClassDomain entryClassDomain = f.createClassDomain(AvlNode.class);
//         entry.addClassDomain(entryClassDomain);
//         entryClassDomain.includeInIsomorphismCheck(true);
    
        
//         IIntSet sizes = f.createIntSet(minSize, maxSize);

//         IIntSet height = f.createIntSet(0, numAvlNode);

// //      IObjSet values = f.createObjSet(Integer.class);
// //      IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
// //      elemsClassDomain.includeInIsomorphismCheck(false);
// //      for (int i = 1; i <= numData; i++)
// //          elemsClassDomain.addObject(new Integer(i));
// //      values.addClassDomain(elemsClassDomain);
// //      values.setNullAllowed(false); //not null allowed

//         IIntSet values = f.createIntSet(0, numData -1);
//         f.set("root", entry);
//         f.set("size", sizes);
//         f.set(AvlNode.class, "data", values);
//         f.set("AvlNode.height", height);        
//         f.set("AvlNode.left", entry);
//         f.set("AvlNode.right", entry);
    
//         return f;

//     }

    // /**To generate AvlTrees that have a given number of nodes, the Korat
    // search algorithm uses the ﬁnitization method.
    // In this method we specify bounds on th number of objects to be used to 
    // construct instances of the data structure, as well as possible values 
    // stored in the ﬁelds of those objects.
    //  */
    public static IFinitization finAvlTree(int numAvlNode, int minSize,
            int maxSize,int numData)  {

        IFinitization f = FinitizationFactory.create(AvlTree.class);

        IObjSet entry = f.createObjSet(AvlNode.class,numAvlNode);
        entry.setNullAllowed(true);
        IClassDomain entryClassDomain = f.createClassDomain(AvlNode.class);
        entry.addClassDomain(entryClassDomain);
        entryClassDomain.includeInIsomorphismCheck(false);
    
        
        IIntSet sizes = f.createIntSet(minSize, maxSize);

        IIntSet height = f.createIntSet(0, numAvlNode);

        IObjSet elems = f.createObjSet(Integer.class);
        IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
        elemsClassDomain.includeInIsomorphismCheck(false);
        for (int i = 1; i <= numData; i++)
            elemsClassDomain.addObject(new Integer(i));
        elems.addClassDomain(elemsClassDomain);
        elems.setNullAllowed(false); //not null allowed

        f.set("root", entry);
        f.set("size", sizes);
        f.set(AvlNode.class, "data", elems);
        f.set("AvlNode.height", height);        
        f.set("AvlNode.left", entry);
        f.set("AvlNode.right", entry);


        return f;

    }
        
}
