#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

cases="bheapkorat.BinomialHeap bheap.BinomialHeap avlfix.AvlTree avl1.AvlTree rbt.TreeSet rbtkiasan.TreeSet bintree1.BinTree list.SinglyLinkedList cdlist.LinkedList cList.NodeCachingLinkedList"
budgets="3 4 5 6 7 8 9 10"

config="DEFAULT SM BLD NoOpt"
for optimization in $config 
do
	for casestudy in $cases 
	do
	    for budget in $budgets
	    do
	        cmd="timeout $TO ./beapi-optimizations.sh 3_fajita $casestudy $budget $optimization"
	        bash -c "$cmd"
	        if [ $? -eq 124 ]; then 
	            echo ">> Execution timed out"
	            break;
	        fi
	    done
	done
done


process_results_optimizations;    
