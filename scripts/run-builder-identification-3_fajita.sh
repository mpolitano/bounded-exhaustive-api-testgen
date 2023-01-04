#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="bheapkorat.BinomialHeap bheap.BinomialHeap avlfix.AvlTree avl1.AvlTree rbt.TreeSet rbtkiasan.TreeSet bintree1.BinTree list.SinglyLinkedList cdlist.LinkedList cList.NodeCachingLinkedList"

for casestudy in $cases 
do
    cmd="timeout $TO ./run-builder-identification.sh 2_roops $casestudy"
    bash -c "$cmd"
    if [ $? -eq 124 ]; then 
        echo ">> Execution timed out"
        break;
    fi
done

process_results_builders;

