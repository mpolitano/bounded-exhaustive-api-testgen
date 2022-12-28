//import gnu.trove.THashMap.KeyView.EntryIterator;
package redblacktree;


import java.util.NoSuchElementException;

import korat.finitization.IBooleanSet;
import korat.finitization.IClassDomain;
import korat.finitization.IFinitization;
import korat.finitization.IIntSet;
import korat.finitization.IObjSet;
import korat.finitization.impl.FinitizationFactory;

public class TreeMap<V> implements java.io.Serializable {

    /**
	 * 
	 */
	private static final long serialVersionUID = -579631227897002033L;

	//@ invariant (root == null || root.consistency()) && size == realSize();
	public boolean repOK() {
		return (root == null || root.consistency()) && size == realSize();
	}

    public static IFinitization finTreeMap(int maxSize) {
    	return finTreeMap(maxSize, maxSize, 0, maxSize -1);
    }
	
    static IFinitization finTreeMap(int numEntries, int maxSize, int minKey, int maxKey) {
        IFinitization f = FinitizationFactory.create(TreeMap.class);

        IClassDomain entryDomain = f.createClassDomain(Entry.class, numEntries);
        IObjSet entries = f.createObjSet(Entry.class, true);
        entries.addClassDomain(entryDomain);

        IIntSet sizes = f.createIntSet(0, maxSize);

        IIntSet keys = f.createIntSet(minKey, maxKey);

        //IObjSet values = f.createIntSet(minKey, maxKey);
		IObjSet values = f.createObjSet(Integer.class);
		IClassDomain elemsClassDomain = f.createClassDomain(Integer.class);
		elemsClassDomain.includeInIsomorphismCheck(false);
		for (int i = minKey; i <= maxKey; i++)
			elemsClassDomain.addObject(new Integer(i));
		values.addClassDomain(elemsClassDomain);
		values.setNullAllowed(false);

        IBooleanSet colors = f.createBooleanSet();

        f.set("root", entries);
        f.set("size", sizes);
        f.set("Entry.left", entries);
        f.set("Entry.right", entries);
        f.set("Entry.parent", entries);
        f.set("Entry.color", colors);
        f.set("Entry.key", keys);
        f.set("Entry.value", values);

        return f;
    }
	

    private Entry<V> root = null;

    /**
     * The number of entries in the tree
     */
    private int size = 0;

    /**
     * The number of structural modifications to the tree.
     */
    private int modCount = 0;

    private void incrementSize() {
        modCount++;
        size++;
    }

    private void decrementSize() {
        modCount++;
        size--;
    }

    // Query Operations

    /**
     * Returns the number of key-value mappings in this map.
     * 
     * @return the number of key-value mappings in this map.
     */
    public int size() {
        return size;
    }

    /**
     * Returns <tt>true</tt> if this map contains a mapping for the specified
     * key.
     * 
     * @param key
     *            key whose presence in this map is to be tested.
     * 
     * @return <tt>true</tt> if this map contains a mapping for the specified
     *         key.
     * @throws ClassCastException
     *             if the key cannot be compared with the keys currently in the
     *             map.
     * @throws NullPointerException
     *             key is <tt>null</tt> and this map uses natural ordering, or
     *             its comparator does not tolerate <tt>null</tt> keys.
     */
    public boolean containsKey(int key) {
        return getEntry(key) != null;
    }

    /**
     * Returns <tt>true</tt> if this map maps one or more keys to the
     * specified value. More formally, returns <tt>true</tt> if and only if
     * this map contains at least one mapping to a value <tt>value</tt> such that
     * <tt>(value==null ? value==null : value.equals(value))</tt>. This operation
     * will probably require time linear in the Map size for most
     * implementations of Map.
     * 
     * @param value
     *            value whose presence in this Map is to be tested.
     * @return <tt>true</tt> if a mapping to <tt>value</tt> exists;
     *         <tt>false</tt> otherwise.
     * @since 1.2
     */
    public boolean containsValue(Object value) {
        return (root == null ? false : (value == null ? valueSearchNull(root)
                : valueSearchNonNull(root, value)));
    }

    private boolean valueSearchNull(Entry n) {
        if (n.value == null)
            return true;

        // Check left and right subtrees for value
        return (n.left != null && valueSearchNull(n.left))
                || (n.right != null && valueSearchNull(n.right));
    }

    private boolean valueSearchNonNull(Entry n, Object value) {
        // Check this node for the value
        if (value.equals(n.value))
            return true;

        // Check left and right subtrees for value
        return (n.left != null && valueSearchNonNull(n.left, value))
                || (n.right != null && valueSearchNonNull(n.right, value));
    }

    /**
     * Returns the value to which this map maps the specified key. Returns
     * <tt>null</tt> if the map contains no mapping for this key. A return
     * value of <tt>null</tt> does not <i>necessarily</i> indicate that the
     * map contains no mapping for the key; it's also possible that the map
     * explicitly maps the key to <tt>null</tt>. The <tt>containsKey</tt>
     * operation may be used to distinguish these two cases.
     * 
     * @param key
     *            key whose associated value is to be returned.
     * @return the value to which this map maps the specified key, or
     *         <tt>null</tt> if the map contains no mapping for the key.
     * @throws ClassCastException
     *             key cannot be compared with the keys currently in the map.
     * @throws NullPointerException
     *             key is <tt>null</tt> and this map uses natural ordering, or
     *             its comparator does not tolerate <tt>null</tt> keys.
     * 
     * @see #containsKey(Object)
     */
    public V get(int key) {
        Entry<V> p = getEntry(key);
        return (p == null ? null : p.value);
    }


    /**
     * Returns the first (lowest) key currently in this sorted map.
     * 
     * @return the first (lowest) key currently in this sorted map.
     * @throws NoSuchElementException
     *             Map is empty.
     */
    public int firstKey() {
        return key(firstEntry());
    }

    /**
     * Returns the last (highest) key currently in this sorted map.
     * 
     * @return the last (highest) key currently in this sorted map.
     * @throws NoSuchElementException
     *             Map is empty.
     */
    public int lastKey() {
        return key(lastEntry());
    }


    /**
     * Returns this map's entry for the given key, or <tt>null</tt> if the map
     * does not contain an entry for the key.
     * 
     * @return this map's entry for the given key, or <tt>null</tt> if the map
     *         does not contain an entry for the key.
     * @throws ClassCastException
     *             if the key cannot be compared with the keys currently in the
     *             map.
     * @throws NullPointerException
     *             key is <tt>null</tt> and this map uses natural order, or
     *             its comparator does not tolerate * <tt>null</tt> keys.
     */
    private Entry<V> getEntry(int key) {
        Entry<V> p = root;
        int k =  key;
        while (p != null) {
            //int cmp = compare(k, p.key);
            if (k == p.key)
                return p;
            else if (k < p.key)
                p = p.left;
            else
                p = p.right;
        }
        return null;
    }


    /**
     * Returns the key corresponding to the specified Entry. Throw
     * NoSuchElementException if the Entry is <tt>null</tt>.
     */
    private static int key(Entry<?> e) {
        if (e == null)
            throw new NoSuchElementException();
        return e.key;
    }

    /**
     * Associates the specified value with the specified key in this map. If the
     * map previously contained a mapping for this key, the old value is
     * replaced.
     * 
     * @param key
     *            key with which the specified value is to be associated.
     * @param value
     *            value to be associated with the specified key.
     * 
     * @return previous value associated with specified key, or <tt>null</tt>
     *         if there was no mapping for key. A <tt>null</tt> return can
     *         also indicate that the map previously associated <tt>null</tt>
     *         with the specified key.
     * @throws ClassCastException
     *             key cannot be compared with the keys currently in the map.
     * @throws NullPointerException
     *             key is <tt>null</tt> and this map uses natural order, or
     *             its comparator does not tolerate <tt>null</tt> keys.
     */
    //@ ensures root != null;
    public V put(int key, V value) {
        Entry<V> t = root;

        if (t == null) {
            incrementSize();
            root = new Entry<V>(key, value, null);
            return null;
        }

        while (true) {
            int cmp = compare(key, t.key);
            if (cmp == 0) {
                return t.setValue(value);
            } else if (cmp < 0) {
                if (t.left != null) {
                    t = t.left;
                } else {
                    incrementSize();
                    t.left = new Entry<V>(key, value, t);
                    fixAfterInsertion(t.left);
                    return null;
                }
            } else { // cmp > 0
                if (t.right != null) {
                    t = t.right;
                } else {
                    incrementSize();
                    t.right = new Entry<V>(key, value, t);
                    fixAfterInsertion(t.right);
                    return null;
                }
            }
        }
        //return null;
    }

    /**
     * Removes the mapping for this key from this TreeMap if present.
     * 
     * @param key
     *            key for which mapping should be removed
     * @return previous value associated with specified key, or <tt>null</tt>
     *         if there was no mapping for key. A <tt>null</tt> return can
     *         also indicate that the map previously associated <tt>null</tt>
     *         with the specified key.
     * 
     * @throws ClassCastException
     *             key cannot be compared with the keys currently in the map.
     * @throws NullPointerException
     *             key is <tt>null</tt> and this map uses natural order, or
     *             its comparator does not tolerate <tt>null</tt> keys.
     */
    public V remove(int key) {
        Entry<V> p = getEntry(key);
        if (p == null)
            return null;

        V oldValue = p.value;
        deleteEntry(p);
        return oldValue;
    }
    private int realSize() {
        if(root==null) {
            return 0;
        }
        return root.size();
    }

    /**
     * Removes all mappings from this TreeMap.
     */
    public void clear() {
        modCount++;
        size = 0;
        root = null;
    }

    /**
     * Compares two keys using the correct comparison method for this TreeMap.
     */
    private int compare(int k1, int k2) {
        if(k1 < k2) {
            return -1;
            
        }else if(k1==k2) {
            return 0;
        }else {
            return 1;
        }
    }

    /**
     * Test two values for equality. Differs from o1.equals(o2) only in that it
     * copes with <tt>null</tt> o1 properly.
     */
    static boolean valEquals(Object o1, Object o2) {
        return (o1 == null ? o2 == null : o1.equals(o2));
    }

    static final boolean RED = false;

    static final boolean BLACK = true;

    /**
     * Returns the first Entry in the TreeMap (according to the TreeMap's
     * key-sort function). Returns null if the TreeMap is empty.
     */
    private Entry<V> firstEntry() {
        Entry<V> p = root;
        if (p != null)
            while (p.left != null)
                p = p.left;
        return p;
    }

    /**
     * Returns the last Entry in the TreeMap (according to the TreeMap's
     * key-sort function). Returns null if the TreeMap is empty.
     */
    private Entry<V> lastEntry() {
        Entry<V> p = root;
        if (p != null)
            while (p.right != null)
                p = p.right;
        return p;
    }

    /**
     * Returns the successor of the specified Entry, or null if no such.
     */
    private Entry<V> successor(Entry<V> t) {
        if (t == null)
            return null;
        else if (t.right != null) {
            Entry<V> p = t.right;
            while (p.left != null)
                p = p.left;
            return p;
        } else {
            Entry<V> p = t.parent;
            Entry<V> ch = t;
            while (p != null && ch == p.right) {
                ch = p;
                p = p.parent;
            }
            return p;
        }
    }

    /**
     * Balancing operations.
     * 
     * Implementations of rebalancings during insertion and deletion are
     * slightly different than the CLR version. Rather than using dummy
     * nilnodes, we use a set of accessors that deal properly with null. They
     * are used to avoid messiness surrounding nullness checks in the main
     * algorithms.
     */

    private static < V> boolean colorOf(Entry<V> p) {
        return (p == null ? BLACK : p.color);
    }

    private static < V> Entry<V> parentOf(Entry<V> p) {
        return (p == null ? null : p.parent);
    }

    private static <V> void setColor(Entry<V> p, boolean c) {
        if (p != null)
            p.color = c;
    }

    private static <V> Entry<V> leftOf(Entry<V> p) {
        return (p == null) ? null : p.left;
    }

    private static <V> Entry<V> rightOf(Entry<V> p) {
        return (p == null) ? null : p.right;
    }

    /** From CLR * */
    private void rotateLeft(Entry<V> p) {
        Entry<V> r = p.right;
        p.right = r.left;
        if (r.left != null)
            r.left.parent = p;
        r.parent = p.parent;
        if (p.parent == null)
            root = r;
        else if (p.parent.left == p)
            p.parent.left = r;
        else
            p.parent.right = r;
        r.left = p;
        p.parent = r;
    }

    /** From CLR * */
    private void rotateRight(Entry<V> p) {
        Entry<V> l = p.left;
        p.left = l.right;
        if (l.right != null)
            l.right.parent = p;
        l.parent = p.parent;
        if (p.parent == null)
            root = l;
        else if (p.parent.right == p)
            p.parent.right = l;
        else
            p.parent.left = l;
        l.right = p;
        p.parent = l;
    }

    /** From CLR * */
    private void fixAfterInsertion(Entry<V> x) {
        x.color = RED;

        while (x != null && x != root && x.parent.color == RED) {
            if (parentOf(x) == leftOf(parentOf(parentOf(x)))) {
                Entry<V> y = rightOf(parentOf(parentOf(x)));
                if (colorOf(y) == RED) {
                    setColor(parentOf(x), BLACK);
                    setColor(y, BLACK);
                    setColor(parentOf(parentOf(x)), RED);
                    x = parentOf(parentOf(x));
                } else {
                    if (x == rightOf(parentOf(x))) {
                        x = parentOf(x);
                        rotateLeft(x);
                    }
                    setColor(parentOf(x), BLACK);//bug seeded
                    setColor(parentOf(parentOf(x)), RED);
                    if (parentOf(parentOf(x)) != null)
                        rotateRight(parentOf(parentOf(x)));
                }
            } else {
                Entry<V> y = leftOf(parentOf(parentOf(x)));
                if (colorOf(y) == RED) {
                    setColor(parentOf(x), BLACK);
                    setColor(y, BLACK);
                    setColor(parentOf(parentOf(x)), RED);
                    x = parentOf(parentOf(x));
                } else {
                    if (x == leftOf(parentOf(x))) {
                        x = parentOf(x);
                        rotateRight(x);
                    }
                    setColor(parentOf(x), BLACK);
                    setColor(parentOf(parentOf(x)), RED);
                    if (parentOf(parentOf(x)) != null)
                        rotateLeft(parentOf(parentOf(x)));
                }
            }
        }
        root.color = BLACK;
    }

    /**
     * Delete node p, and then rebalance the tree.
     */
    //@ requires p.wellConnected(p.parent);
    private void deleteEntry(//@NonNull
    Entry<V> p) {
        decrementSize();

        // If strictly internal, copy successor's element to p and then make p
        // point to successor.
        if (p.left != null && p.right != null) {
            Entry<V> s = successor(p);
            p.key = s.key;
            p.value = s.value;
            p = s;
        } // p has 2 children

        // Start fixup at replacement node, if it exists.
        Entry<V> replacement = (p.left != null ? p.left : p.right);

        if (replacement != null) {
            // Link replacement to parent
            replacement.parent = p.parent;
            if (p.parent == null)
                root = replacement;
            else if (p == p.parent.left)
                p.parent.left = replacement;
            else
                p.parent.right = replacement;

            // Null out links so they are OK to use by fixAfterDeletion.
            p.left = p.right = p.parent = null;

            // Fix replacement
            if (p.color == BLACK)
                fixAfterDeletion(replacement);
        } else if (p.parent == null) { // return if we are the only node.
            root = null;
        } else { // No children. Use self as phantom replacement and unlink.
            if (p.color == BLACK)
                fixAfterDeletion(p);

            if (p.parent != null) {
                if (p == p.parent.left)
                    p.parent.left = null;
                else if (p == p.parent.right)
                    p.parent.right = null;
                p.parent = null;
            }
        }
    }

    /** From CLR * */
    private void fixAfterDeletion(Entry<V> x) {
        while (x != root && colorOf(x) == BLACK) {
            if (x == leftOf(parentOf(x))) {
                Entry<V> sib = rightOf(parentOf(x));

                if (colorOf(sib) == RED) {
                    setColor(sib, BLACK);
                    setColor(parentOf(x), RED);
                    rotateLeft(parentOf(x));
                    sib = rightOf(parentOf(x));
                }

                if (colorOf(leftOf(sib)) == BLACK
                        && colorOf(rightOf(sib)) == BLACK) {
                    setColor(sib, RED);
                    x = parentOf(x);
                } else {
                    if (colorOf(rightOf(sib)) == BLACK) {
                        setColor(leftOf(sib), BLACK);
                        setColor(sib, RED);
                        rotateRight(sib);
                        sib = rightOf(parentOf(x));
                    }
                    setColor(sib, colorOf(parentOf(x)));
                    setColor(parentOf(x), BLACK);
                    setColor(rightOf(sib), BLACK);
                    rotateLeft(parentOf(x));
                    x = root;
                }
            } else { // symmetric
                Entry<V> sib = leftOf(parentOf(x));

                if (colorOf(sib) == RED) {
                    setColor(sib, BLACK);
                    setColor(parentOf(x), RED);
                    rotateRight(parentOf(x));
                    sib = leftOf(parentOf(x));
                }

                if (colorOf(rightOf(sib)) == BLACK
                        && colorOf(leftOf(sib)) == BLACK) {
                    setColor(sib, RED);
                    x = parentOf(x);
                } else {
                    if (colorOf(leftOf(sib)) == BLACK) {
                        setColor(rightOf(sib), BLACK);
                        setColor(sib, RED);
                        rotateLeft(sib);
                        sib = leftOf(parentOf(x));
                    }
                    setColor(sib, colorOf(parentOf(x)));
                    setColor(parentOf(x), BLACK);
                    setColor(leftOf(sib), BLACK);
                    rotateRight(parentOf(x));
                    x = root;
                }
            }
        }

        setColor(x, BLACK);
    }
}
