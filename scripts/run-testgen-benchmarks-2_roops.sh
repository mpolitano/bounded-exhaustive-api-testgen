#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="fibheap.FibHeap rbt.TreeSet bheap.BinomialHeap avl.AvlTree linkedlist.LinkedList singlelist.SinglyLinkedList bintree.BinTree ncl.NodeCachingLinkedList"
techniques="beapi korat"
budgets="3"


for casestudy in $cases 
do
    for technique in $techniques 
    do
        for budget in $budgets
        do
            cmd="timeout $TO ./run-testgen-benchmarks.sh 2_roops $casestudy $technique $budget"
            bash -c "$cmd"
            if [ $? -eq 124 ]; then 
                echo ">> Execution timed out"
                break;
            fi
        done
    done
done


# process_results_beapi_vs_korat;
    
