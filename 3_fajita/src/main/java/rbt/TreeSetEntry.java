package  rbt;

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
	private static final long serialVersionUID = 2709100991639329794L;
	public int key;
	public /*@ nullable @*/TreeSetEntry parent;

	//public boolean color = false;
	public int color = 0;
	
	public /*@ nullable @*/TreeSetEntry left = null;
	public /*@ nullable @*/TreeSetEntry right = null;
	

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

}

	/* end roops.core.objects */

