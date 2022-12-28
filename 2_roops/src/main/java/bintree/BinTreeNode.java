//$category roops.core.objects

package bintree;
//Authors: Marcelo Frias
public class BinTreeNode implements java.io.Serializable {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;


	public int key;

	public /*@ nullable @*/BinTreeNode left;

	public /*@ nullable @*/BinTreeNode right;

	public /*@ nullable @*/BinTreeNode parent;

	public BinTreeNode() {}
}

//$endcategory roops.core.objects

