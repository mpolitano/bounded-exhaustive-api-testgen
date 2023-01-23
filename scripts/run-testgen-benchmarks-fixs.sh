#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh
budgetMax="$1"

function run_korat(){
for casestudy in $cases 
do
	for budget in $(seq 3 $budgetMax) 
	do
		cmd="timeout $TO ./run-testgen-benchmarks.sh $package $casestudy korat $budget"
		bash -c "$cmd"
	    if [ $? -eq 124 ]; then 
	        echo ">> Execution timed out"
	        break;
	    fi


	done
done
}

package="0_korat"
cases="korat.examples.redblacktree.RedBlackTree_fix"
run_korat;

package="1_kiasan"
cases="binaryheap.BinaryHeap_fix"
run_korat

package="2_roops"
cases="bintree.BinTree_fix ncl.NodeCachingLinkedList_fix avl.AvlTree_fix rbt.TreeSet_fix"
run_korat

package="3_fajita"
cases="avl.AvlTree_fix"
run_korat





