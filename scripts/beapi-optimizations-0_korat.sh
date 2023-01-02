#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

cases="korat.examples.singlylinkedlist.SinglyLinkedList korat.examples.binheap.BinomialHeap korat.examples.redblacktree.RedBlackTree korat.examples.doublylinkedlist.DoublyLinkedList korat.examples.searchtree.SearchTree korat.examples.fibheap.FibonacciHeap korat.examples.sortedlist.SortedList"
budgets="3"

for casestudy in $cases 
do
    for budget in $budgets
    do
        cmd="timeout $TO ./beapi-optimizations.sh 0_korat $casestudy $budget"
        bash -c "$cmd"
        if [ $? -eq 124 ]; then 
            echo ">> Execution timed out"
            break;
        fi
    done
done


process_results_optimizations;    