#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="korat.examples.singlylinkedlist.SinglyLinkedList korat.examples.sortedlist.SortedList korat.examples.binheap.BinomialHeap korat.examples.redblacktree.RedBlackTree korat.examples.doublylinkedlist.DoublyLinkedList korat.examples.searchtree.SearchTree korat.examples.fibheap.FibonacciHeap"
techniques="beapi korat"
budgetMax="$1"


for casestudy in $cases 
do
    for technique in $techniques 
    do
        for budget in $(seq 3 $budgetMax)
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
    
