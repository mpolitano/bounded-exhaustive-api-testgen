#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="redblacktree.TreeMap redblacktree.TreeSet doublylinkedlist.DoubleLinkedList binarysearchtree.BinarySearchTree disjointSet.orig.DisjSets disjointSet.fast.DisjSetsFast stack.list.StackLi stack.array.StackAr binaryheap.BinaryHeap"
budgets="3 4 5 6 7 8 9 10"

config="DEFAULT SM BLD NoOpt"
for optimization in $config 
do
	for casestudy in $cases 
	do
	    for budget in $budgets
	    do
	        cmd="timeout $TO ./beapi-optimizations.sh 1_kiasan $casestudy $budget $optimization"
	        bash -c "$cmd"
	        if [ $? -eq 124 ]; then 
	            echo ">> Execution timed out"
	            break;
	        fi
	    done
	done
done



# process_results_optimizations;    
