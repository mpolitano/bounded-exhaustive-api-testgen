package cotas.cdlist;

import java.util.ArrayList;

public class Bound4 {

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
	 	next: n0={0,2,0,0};n1={0,3,0,0};n2={0,4,0,0};n3={0,0,0,0};
		prev: n0={0,2,3,4};n1={1,0,0,0};n2={2,0,0,0};n3={3,0,0,0};
	 * */

	//	public Bound4(){
	//		initNext();
	//		initPrevious();
	//		
	//	}

	public static void initPrevious(){

		//4 prev: 
		int [] n0={0,2,3,4};
		int [] n1={1,0,0,0};
		int [] n2={2,0,0,0};
		int [] n3={3,0,0,0};

		previous.add(n0);
		previous.add(n1);
		previous.add(n2);
		previous.add(n3);
	}



	public static void initNext(){

		//Cota 4
		int [] n0={0,2,0,0};
		int [] n1={0,3,0,0};
		int [] n2={0,4,0,0};
		int [] n3={0,0,0,0};

		next.add(n0);
		next.add(n1);
		next.add(n2);
		next.add(n3);

	}


}
