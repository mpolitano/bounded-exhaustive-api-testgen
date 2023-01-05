#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="bheap.BinomialHeap avl.AvlTree rbt.TreeSet bintree.BinTree list.SinglyLinkedList cdlist.LinkedList cList.NodeCachingLinkedList"
techniques="beapi korat"
budgetMax="$1"


for casestudy in $cases 
do
    for technique in $techniques 
    do
        for budget in $(seq 3 $budgetMax)
        do
            cmd="timeout $TO ./run-testgen-benchmarks.sh 3_fajita $casestudy $technique $budget"
            bash -c "$cmd"
            if [ $? -eq 124 ]; then 
                echo ">> Execution timed out"
                break;
            fi
        done
    done
done
    
