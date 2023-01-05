#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="fibheap.FibHeap rbt.TreeSet bheap.BinomialHeap avl.AvlTree linkedlist.LinkedList bintree.BinTree ncl.NodeCachingLinkedList"
techniques="beapi korat"
budgetMax="$1"


for casestudy in $cases 
do
    for technique in $techniques 
    do
        for budget in $(seq 3 $budgetMax)
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
    
