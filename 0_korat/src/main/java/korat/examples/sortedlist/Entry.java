 package korat.examples.sortedlist;

 import java.io.Serializable;
 
 public class Entry implements Serializable {
        /**
         * 
         */
        private static final long serialVersionUID = 1L;

        public int element;

        public Entry next;

        public Entry previous;

        public String toString() {
            return "[" + ( element ) + "]";
        }
    }