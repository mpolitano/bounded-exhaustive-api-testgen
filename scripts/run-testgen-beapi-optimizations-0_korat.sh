#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="korat.examples.singlylinkedlist.SinglyLinkedList korat.examples.binheap.BinomialHeap korat.examples.redblacktree.RedBlackTree korat.examples.doublylinkedlist.DoublyLinkedList korat.examples.searchtree.SearchTree korat.examples.fibheap.FibonacciHeap korat.examples.sortedlist.SortedList"
budgetMax="$1"

config="DEFAULT SM BLD NoOpt"
for optimization in $config 
do
	for casestudy in $cases 
	do
	    for budget in $(seq 3 $budgetMax)
	    do
	        cmd="timeout $TO ./run-testgen-beapi-optimizations.sh 0_korat $casestudy $budget $optimization"
	        bash -c "$cmd"
	        if [ $? -eq 124 ]; then 
	            echo ">> Execution timed out"
	            break;
	        fi
	    done
	done
done


# process_results_optimizations;    