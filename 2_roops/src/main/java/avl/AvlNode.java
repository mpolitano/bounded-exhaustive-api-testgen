package avl;

//$category roops.core.objects

public class AvlNode implements java.io.Serializable{

	/**
	 * 
	 */
	private static final long serialVersionUID = 5324094080130191194L;

	int element; 

	/*@ nullable @*/AvlNode left; 

	/*@ nullable @*/AvlNode right; 

	int height; // Height

    public AvlNode() {}
    public AvlNode(int e) { element = e; }
}

//$endcategory roops.core.objects

