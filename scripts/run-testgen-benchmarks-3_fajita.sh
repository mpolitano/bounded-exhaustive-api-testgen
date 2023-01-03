#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="bheapkorat.BinomialHeap bheap.BinomialHeap avlfix.AvlTree avl1.AvlTree rbt.TreeSet rbtkiasan.TreeSet bintree1.BinTree list.SinglyLinkedList cdlist.LinkedList cList.NodeCachingLinkedList"
techniques="beapi korat"
budgets="3"


for casestudy in $cases 
do
    for technique in $techniques 
    do
        for budget in $budgets
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


# process_results_beapi_vs_korat;
    
