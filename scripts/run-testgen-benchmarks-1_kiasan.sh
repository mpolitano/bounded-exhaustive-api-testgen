#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

cases="redblacktree.TreeMap doublylinkedlist.DoubleLinkedList binarysearchtree.BinarySearchTree disjointSet.orig.DisjSets disjointSet.fast.DisjSetsFast stack.list.StackLi stack.array.StackAr binaryheap.BinaryHeap"
techniques="beapi korat"
budgets="3"


for casestudy in $cases 
do
    for technique in $techniques 
    do
        for budget in $budgets
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


process_results_beapi_vs_korat;
    
