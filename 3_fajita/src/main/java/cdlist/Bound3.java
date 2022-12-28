package cotas.cdlist;

import java.util.ArrayList;

public class Bound3 {

	private static ArrayList<int[]> next = new ArrayList<int[]>();
	private static ArrayList<int[]> previous = new ArrayList<int[]>();
	//private static ArrayList<int[]> root = new ArrayList<int[]>();
	/**
	 	next: n0={0,2,0};n1={0,3,0};n2={0,0,0};
	    prev: n0={0,2,3};n1={1,0,0};n2={2,0,0};
	 * */

	//	public Bound3(){
	//		initNext();
	//		initPrevious();
	//		
	//	}

	
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

	public static void initPrevious(){

		//3 prev: 
		int [] n0={1,2,0};//{0,2,3};
		int [] n1={1,3,0};
		int [] n2={1,0,0};
		
		
//		prev: n0={0,2,3};n1={1,0,0};n2={2,0,0};
	

		previous.add(n0);
		previous.add(n1);
		previous.add(n2);

	}



	public static void initNext(){

		//Cota 3
		int [] n0={1,2,3};//{0,2,0};
		int [] n1={1,3,0};//{0,3,0};
		int [] n2={1,2,0};

		//next: n0={0,2,0};n1={0,3,0};n2={1,0,0};

		
		next.add(n0);
		next.add(n1);
		next.add(n2);
	}


}
