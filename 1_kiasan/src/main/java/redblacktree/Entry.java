package redblacktree;

/**
 * Node in the Tree. Doubles as a means to pass key-value pairs back to user
 * (see Map.Entry).
 */

public class Entry<V> implements java.io.Serializable {
    /**
	 * 
	 */
	private static final long serialVersionUID = 6741853057020723578L;

	int key;

    V value;

    Entry<V> left = null;

    Entry<V> right = null;

    Entry<V> parent;

    boolean color = TreeMap.BLACK;
    public Entry() {
        parent=null;
        value=null;
        key=-1;
    }

    /**
     * Make a new cell with given key, value, and parent, and with
     * <tt>null</tt> child links, and BLACK color.
     */
    Entry(int key, V value, Entry<V> parent) {
        this.key = key;
        this.value = value;
        this.parent = parent;
    }
    public boolean consistency()
    {
        return wellConnected(null) && redConsistency() && blackConsistency() && ordered();
    }
    boolean ordered() {
        return ordered(this,new Range());
    }
    boolean ordered(Entry<V> t, Range range) {
        if(t == null) {
            return true;
        }
        if(!range.inRange(t.key)) {
            return false;
        }
        boolean ret=true;
        ret = ret && ordered(t.left,range.setUpper(t.key));
        ret = ret && ordered(t.right,range.setLower(t.key));
        return ret;
    }
    int size() {
        int ls=0,rs=0;
        if(left!=null) {
            ls=left.size();
        }
        if(right!=null) {
            rs=right.size();
        }
        return 1+ls+rs;
    }
    /**
     * Returns true iff this tree is well-connected.
     */

    public boolean wellConnected(Entry<V> expectedParent) {
        boolean ok = true;
        if (expectedParent != parent) {

            return false;
        }
        
        if (right != null) {
            //ok && is redundant because ok is assigned true
            ok = ok && right.wellConnected(this);
        }
        
        if (left != null) {
            
            ok = ok && left.wellConnected(this);
        }
        
        if(right==left && right!=null && left!=null) {//left!=null is redundant because left==right && right!=null
            return false;
        }
        
        return ok;
    }

    /**
     * Returns true if no red node in subtree has red children
     * 
     * @post returns true if no red node in subtree has red children
     */
    protected boolean redConsistency() {
        boolean ret = true;
        if (color == TreeMap.RED
                && ((left != null && left.color == TreeMap.RED) || (right != null && right.color == TreeMap.RED)))
            return false;
        if (left != null) {
            ret = ret && left.redConsistency();
        }
        if (right != null) {
            ret = ret && right.redConsistency();
        }
        return ret;
    }

    /**
     * Returns the black height of this subtree.
     * 
     * @pre
     * @post returns the black height of this subtree
     */
    protected int blackHeight() {
        int ret = 0;
        if (color == TreeMap.BLACK) {
            ret = 1;
        }
        if (left != null) {
            ret += left.blackHeight();
        }
        return ret;
    }

    /**
     * Returns true if black properties of tree are correct
     * 
     * @post returns true if black properties of tree are correct
     */
    protected boolean blackConsistency() {

        if (color != TreeMap.BLACK) // root must be black
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
     * Checks to make sure that the black height of tree is height
     * 
     * @post checks to make sure that the black height of tree is height
     */
    protected boolean consistentlyBlackHeight(int height) {
        boolean ret = true;
        if (color == TreeMap.BLACK)
            height--;
        if (left == null) {
            ret = ret && (height == 0);
        } else {
            ret = ret && (left.consistentlyBlackHeight(height));
        }
        if (right == null) {
            ret = ret && (height == 0);
        } else {
            ret = ret && (right.consistentlyBlackHeight(height));
        }

        return ret;
    }

    /**
     * Returns the key.
     * 
     * @return the key.
     */
    public int getKey() {
        return key;
    }

    /**
     * Returns the value associated with the key.
     * 
     * @return the value associated with the key.
     */
    public V getValue() {
        return value;
    }

    /**
     * Replaces the value currently associated with the key with the given
     * value.
     * 
     * @return the value associated with the key before this method was
     *         called.
     */
    public V setValue(V value) {
        V oldValue = this.value;
        this.value = value;
        return oldValue;
    }

    public boolean equals(Object o) {
        if (!(o instanceof Entry))
            return false;
        Entry e = (Entry) o;

        return key== e.getKey() && TreeMap.valEquals(value, e.getValue());
    }

    public int hashCode() {
        int keyHash = key;
        int valueHash = (value == null ? 0 : value.hashCode());
        return keyHash ^ valueHash;
    }

    public String toString() {
        return key + "=" + value;
    }
}