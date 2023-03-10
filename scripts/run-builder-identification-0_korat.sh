#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="korat.examples.singlylinkedlist.SinglyLinkedList korat.examples.sortedlist.SortedList korat.examples.binheap.BinomialHeap korat.examples.redblacktree.RedBlackTree korat.examples.doublylinkedlist.DoublyLinkedList korat.examples.searchtree.SearchTree korat.examples.fibheap.FibonacciHeap"


for casestudy in $cases 
do
    cmd="timeout $TO ./run-builder-identification.sh 0_korat $casestudy"
    bash -c "$cmd"
    if [ $? -eq 124 ]; then 
        echo ">> Execution timed out"
        break;
    fi
done
