package  redblacktree;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

/**
 * @SpecField blackHeight : int from this.left, this.right |
 * (
 *		( this.left=null && this.right=null => this.blackHeight=1 ) && 
 *
 *		( this.left!=null && this.right=null => ( 
 *		        ( ( this in this.left.*(left@+right)@-null ) => this.blackHeight=0 ) && 
 *		        ( ( this !in this.left.*(left@+right)@-null ) => ( 
 *		                ( this.left.color=true  => this.blackHeight=this.left.blackHeight +1 ) && 
 *		                ( this.left.color=false => this.blackHeight=this.left.blackHeight )  
 *		         ))
 *		                                        )) && 
 *		( this.left=null && this.right!=null => ( 
 *		        ( ( this in this.right.*(left@+right)@-null ) => this.blackHeight=0 ) && 
 *		        ( ( this !in this.right.*(left@+right)@-null ) => ( 
 *		                ( this.right.color=true  => this.blackHeight=this.right.blackHeight +1 ) && 
 *		                ( this.right.color=false => this.blackHeight=this.right.blackHeight )  
 *		         ))
 *		                                        )) &&
 * 
 *		( this.left!=null && this.right!=null => ( 
 *		        ( ( this in this.^(left@+right)@-null ) => this.blackHeight=0 ) && 
 *		        ( ( this !in this.^(left@+right)@-null ) => ( 
 *		                ( this.left.color=true  => this.blackHeight=this.left.blackHeight +1 ) && 
 *		                ( this.left.color=false => this.blackHeight=this.left.blackHeight )  
 *		                                        ))
 *		         ))                                  
 *
 * ) ;
 */
public class TreeSetEntry implements Serializable {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 9052271800608983105L;
	int key;
	/*@ nullable @*/TreeSetEntry parent;

	//public boolean color = false;
	int color = 0;
	
	/*@ nullable @*/TreeSetEntry left = null;
	/*@ nullable @*/TreeSetEntry right = null;
	

	public TreeSetEntry() {}

	public String toStrings() {
		Set<TreeSetEntry> visited = new HashSet<TreeSetEntry>();
		visited.add(this);
		return tostring(visited);
	}

	private String tostring(Set<TreeSetEntry> visited) {
		StringBuffer buf = new StringBuffer();
		// buf.append(" ");
		// buf.append(System.identityHashCode(this));
		buf.append(" {");
		if (left != null)
			if (visited.add(left))
				buf.append(left.tostring(visited));
			else
				buf.append("!tree");

		buf.append("" + this.tostringInfoNode() + "");
		if (right != null)
			if (visited.add(right))
				buf.append(right.tostring(visited));
			else
				buf.append("!tree");
		buf.append("} ");
		return buf.toString();
	}

	
	private String toStringColor(){
		if (this.color ==0 )
			return "R";
		else
			return "B";
	}

	private String toStringParent(){
		if (this.parent==null){
			return "null";
		}
		else
			return String.valueOf((this.parent.key));
	} 

	private String tostringInfoNode() {
		StringBuffer buf = new StringBuffer();
		buf.append(" (");
		buf.append("" + this.key + ",");
		buf.append("" + this.toStringColor() + ",");
		buf.append("" + this.toStringParent() + " )");
		return buf.toString();
	}
	
    int size() {
        int ls = 0, rs = 0;
        if (this.left != null) {
          ls = this.left.size();
        }
        if (this.right != null) {
          rs = this.right.size();
        }
        return 1 + ls + rs;
      }

	
	/**
	 * Returns true if black properties of tree are correct
	 * 
	 * @post returns true if black properties of tree are correct
	 */
	protected boolean blackConsistency() {

		if (this.color != TreeSet.BLACK) // root must be black
		{
			return false;
		}
		// the number of black nodes on way to any leaf must be same
		if (!consistentlyBlackHeight(blackHeight())) {
			return false;
		}
		return true;
	}

	/**
	 * Returns the black height of this subtree.
	 * 
	 * @pre
	 * @post returns the black height of this subtree
	 */
	private int blackHeight() {
		int ret = 0;
		if (this.color == TreeSet.BLACK) {
			ret = 1;
		}
		if (this.left != null) {
			ret += this.left.blackHeight();
		}
		return ret;
	}
	
	boolean consistency() {
		return wellConnected(null) && redConsistency() && blackConsistency()
				&& ordered();
	}

	/**
	 * Checks to make sure that the black height of tree is height
	 * 
	 * @post checks to make sure that the black height of tree is height
	 */
	private boolean consistentlyBlackHeight(int height) {
		boolean ret = true;
		if (this.color == TreeSet.BLACK) {
			height--;
		}
		if (this.left == null) {
			ret = ret && (height == 0);
		} else {
			ret = ret && (this.left.consistentlyBlackHeight(height));
		}
		if (this.right == null) {
			ret = ret && (height == 0);
		} else {
			ret = ret && (this.right.consistentlyBlackHeight(height));
		}

		return ret;
	}
	
	public boolean ordered() {
		return ordered(this, -1, -1);
	}

	private boolean ordered(TreeSetEntry n, int min, int max) { 	
		if ((min != -1 && n.key <= (min)) || (max != -1 && n.key >= (max)))
            return false;
		if (n.left != null)
			if (!ordered(n.left, min, n.key))
				return false;
		if (n.right != null)
			if (!ordered(n.right, n.key, max))
				return false;
		return true;
	}
	
	/**
	 * Returns true if no red node in subtree has red children
	 * 
	 * @post returns true if no red node in subtree has red children
	 */
	private boolean redConsistency() {
		boolean ret = true;
		if ((this.color == TreeSet.RED)
				&& (((this.left != null) && (this.left.color == TreeSet.RED)) || ((this.right != null) && (this.right.color == TreeSet.RED)))) {
			return false;
		}
		if (this.left != null) {
			ret = ret && this.left.redConsistency();
		}
		if (this.right != null) {
			ret = ret && this.right.redConsistency();
		}
		return ret;
	}
	
	private boolean wellConnected(final TreeSetEntry expectedParent) {
		boolean ok = true;
		if (expectedParent != this.parent) {

			return false;
		}

		if (this.right != null) {
			// ok && is redundant because ok is assigned true
			ok = ok && this.right.wellConnected(this);
		}

		if (this.left != null) {

			ok = ok && this.left.wellConnected(this);
		}

		if ((this.right == this.left) && (this.right != null)
				&& (this.left != null)) {// left!=null
			// is
			// redundant
			// because
			// left==right
			// &&
			// right!=null
			return false;
		}

		return ok;
	}


}

	/* end roops.core.objects */




