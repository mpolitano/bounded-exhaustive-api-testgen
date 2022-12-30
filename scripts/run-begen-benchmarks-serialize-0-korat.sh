#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

cases="korat.examples.singlylinkedlist.SinglyLinkedList korat.examples.binheap.BinomialHeap korat.examples.redblacktree.RedBlackTree korat.examples.doublylinkedlist.DoublyLinkedList korat.examples.searchtree.SearchTree korat.examples.fibheap.FibonacciHeap"
techniques="beapi korat"
minscope=3
maxscope=4

for casestudy in $cases 
do
    for technique in $techniques 
    do
        cmd="timeout $TO ./run-begen-benchmarks-serialize.sh 0_korat $casestudy $minscope $maxscope"
        bash -c "$cmd"
        if [ $? -eq 124 ]; then 
            echo ">> Execution timed out"
            break;
        fi
    done
done


process-results-inclusion.sh;
    
