package cotas.cdlist;

import java.util.ArrayList;

public class Bound2 {

	private static ArrayList<int[]> next = new ArrayList<int[]>();
	private static ArrayList<int[]> previous = new ArrayList<int[]>();
	//private static ArrayList<int[]> root = new ArrayList<int[]>();


	public static ArrayList<int[]> getNextInstance(){
		if (!next.isEmpty()){
			return next;
		}
		else{
			initNext();
			return next;
		}

	}

	public static ArrayList<int[]> getPreviousInstance(){
		if (!previous.isEmpty()){
			return previous;
		}
		else{
			initPrevious();
			return previous;
		}

	}

	/**
	 	next: n0={0,2};n1={0,0};
 	    prev: n0={0,2};n1={1,0};
	* */

	//	public Bound2(){
	//		initNext();
	//		initPrevious();
	//		
	//	}



	public static void initPrevious(){

		//2 prev: 
		int [] n0={1,2};
		int [] n1={1,0};

		//prev: n0={0,2};n1={1,0};
		
		
		previous.add(n0);
		previous.add(n1);
	}



	public static void initNext(){

		//Cota 2
		
		//next: n0={0,2};n1={1,0};
		int [] n0={1,2};
		int [] n1={1,0};

		next.add(n0);
		next.add(n1);
	}


}
