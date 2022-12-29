#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

cases="korat.examples.singlylinkedlist.SinglyLinkedList korat.examples.binheap.BinomialHeap korat.examples.redblacktree.RedBlackTree korat.examples.doublylinkedlist.DoublyLinkedList korat.examples.searchtree.SearchTree korat.examples.fibheap.FibonacciHeap"
techniques="beapi korat"
budgets="3"


for casestudy in $cases 
do
    for technique in $techniques 
    do
        for budget in $budgets
        do
            cmd="timeout $TO ./run-testgen-benchmarks.sh 0_korat $casestudy $technique $budget"
            bash -c "$cmd"
            if [ $? -eq 124 ]; then 
                echo ">> Execution timed out"
                break;
            fi
        done
    done
done


process_results_beapi_vs_korat;
    
