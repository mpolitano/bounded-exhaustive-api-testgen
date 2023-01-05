#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="redblacktree.TreeMap doublylinkedlist.DoubleLinkedList binarysearchtree.BinarySearchTree disjointSet.orig.DisjSets disjointSet.fast.DisjSetsFast stack.list.StackLi stack.array.StackAr binaryheap.BinaryHeap"
techniques="beapi korat"
budgetMax="$1"


for casestudy in $cases 
do
    for technique in $techniques 
    do
        for budget in $(seq 3 $budgetMax)
        do
            cmd="timeout $TO ./run-testgen-benchmarks.sh 1_kiasan $casestudy $technique $budget"
            bash -c "$cmd"
            if [ $? -eq 124 ]; then 
                echo ">> Execution timed out"
                break;
            fi
        done
    done
done
    
