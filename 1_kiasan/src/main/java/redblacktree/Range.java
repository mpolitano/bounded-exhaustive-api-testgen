package redblacktree;

public class Range {
    final int lower;
    final int upper;
    final boolean isPositiveInfinity;
    final boolean isNegativeInfinity;
    public Range() {
        this(0,0,true,true);
    }
    private Range(int u,int l, boolean ip, boolean in) {
        this.upper = u;
        this.lower = l;
        this.isPositiveInfinity=ip;
        this.isNegativeInfinity=in;
    }
    public boolean inRange(int value) {
        boolean ret=true;
        if(!isPositiveInfinity) {
            ret = value < upper;
        }
        if(!isNegativeInfinity) {
            ret = ret && (value > lower);
        }
        return ret;
    }
    public Range setLower(int l) {
        assert isNegativeInfinity || (l>lower);
        return new Range(upper,l,isPositiveInfinity,false);
    }
    public Range setUpper(int u) {
        assert isPositiveInfinity || (u<upper);
        return new Range(u,lower,false,isNegativeInfinity);
    }
}
