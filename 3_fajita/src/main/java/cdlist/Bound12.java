package cotas.cdlist;

import java.util.ArrayList;

public class Bound12 {

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
	 	 next: n0={0,2,0,0,0,0,0,0,0,0,0,0};n1={0,3,0,0,0,0,0,0,0,0,0,0};n2={0,4,0,0,0,0,0,0,0,0,0,0};
		 		n3={0,5,0,0,0,0,0,0,0,0,0,0};n4={0,6,0,0,0,0,0,0,0,0,0,0};n5={0,7,0,0,0,0,0,0,0,0,0,0};
		 		n6={0,8,0,0,0,0,0,0,0,0,0,0};n7={0,9,0,0,0,0,0,0,0,0,0,0};n8={0,10,0,0,0,0,0,0,0,0,0,0};
		 		n9={0,11,0,0,0,0,0,0,0,0,0,0};n10={0,12,0,0,0,0,0,0,0,0,0,0};n11={0,0,0,0,0,0,0,0,0,0,0,0};
	 	prev: n0={0,2,3,4,5,6,7,8,9,10,11,12,13};n1={1,0,0,0,0,0,0,0,0,0,0,0,0};
		n2={2,0,0,0,0,0,0,0,0,0,0,0,0};n3={3,0,0,0,0,0,0,0,0,0,0,0,0};n4={4,0,0,0,0,0,0,0,0,0,0,0,0};
		n5={5,0,0,0,0,0,0,0,0,0,0,0,0};n6={6,0,0,0,0,0,0,0,0,0,0,0,0};n7={7,0,0,0,0,0,0,0,0,0,0,0,0};
		n8={8,0,0,0,0,0,0,0,0,0,0,0,0};n9={9,0,0,0,0,0,0,0,0,0,0,0,0};
			n10={10,0,0,0,0,0,0,0,0,0,0,0,0};n11={11,0,0,0,0,0,0,0,0,0,0,0,0};
			n12={12,0,0,0,0,0,0,0,0,0,0,0,0};
	 * */

	//	public Bound12(){
	//		initNext();
	//		initPrevious();
	//		
	//	}

	public static void initPrevious(){

		//12 prev: 
		int [] n0={0,2,3,4,5,6,7,8,9,10,11,12};
		int [] n1={1,0,0,0,0,0,0,0,0,0,0,0};
		int [] n2={2,0,0,0,0,0,0,0,0,0,0,0};
		int [] n3={3,0,0,0,0,0,0,0,0,0,0,0};
		int [] n4={4,0,0,0,0,0,0,0,0,0,0,0};
		int [] n5={5,0,0,0,0,0,0,0,0,0,0,0};
		int [] n6={6,0,0,0,0,0,0,0,0,0,0,0};
		int [] n7={7,0,0,0,0,0,0,0,0,0,0,0};
		int [] n8={8,0,0,0,0,0,0,0,0,0,0,0};
		int [] n9={9,0,0,0,0,0,0,0,0,0,0,0};
		int [] n10={10,0,0,0,0,0,0,0,0,0,0,0};
		int [] n11={11,0,0,0,0,0,0,0,0,0,0,0};


		previous.add(n0);
		previous.add(n1);
		previous.add(n2);
		previous.add(n3);
		previous.add(n4);
		previous.add(n5);
		previous.add(n6);
		previous.add(n7);
		previous.add(n8);
		previous.add(n9);
		previous.add(n10);
		previous.add(n11);

	}



	public static void initNext(){



		//Cota 12

		int [] n0={0,2,0,0,0,0,0,0,0,0,0,0};
		int [] n1={0,3,0,0,0,0,0,0,0,0,0,0};
		int [] n2={0,4,0,0,0,0,0,0,0,0,0,0};
		int [] n3={0,5,0,0,0,0,0,0,0,0,0,0};
		int [] n4={0,6,0,0,0,0,0,0,0,0,0,0};
		int [] n5={0,7,0,0,0,0,0,0,0,0,0,0};
		int [] n6={0,8,0,0,0,0,0,0,0,0,0,0};
		int [] n7={0,9,0,0,0,0,0,0,0,0,0,0};
		int [] n8={0,10,0,0,0,0,0,0,0,0,0,0};
		int [] n9={0,11,0,0,0,0,0,0,0,0,0,0};
		int [] n10={0,12,0,0,0,0,0,0,0,0,0,0};
		int [] n11={0,0,0,0,0,0,0,0,0,0,0,0};

		next.add(n0);
		next.add(n1);
		next.add(n2);
		next.add(n3);
		next.add(n4);
		next.add(n5);
		next.add(n6);
		next.add(n7);
		next.add(n8);
		next.add(n9);
		next.add(n10);
		next.add(n11);

	}


}
