#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

cases="fibheap.FibHeap rbt.TreeSet bheap.BinomialHeap avl.AvlTree linkedlist.LinkedList singlelist.SinglyLinkedList bintree.BinTree ncl.NodeCachingLinkedList"
budgets="3"

for casestudy in $cases 
do
    for budget in $budgets
    do
        cmd="timeout $TO ./beapi-optimizations.sh 2_roops $casestudy $budget"
        bash -c "$cmd"
        if [ $? -eq 124 ]; then 
            echo ">> Execution timed out"
            break;
        fi
    done
done


process_results_optimizations;    
