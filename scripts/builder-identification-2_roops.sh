#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

cases="fibheap.FibHeap rbt.TreeSet bheap.BinomialHeap avl.AvlTree linkedlist.LinkedList singlelist.SinglyLinkedList bintree.BinTree ncl.NodeCachingLinkedList"


for casestudy in $cases 
do
    cmd="timeout $TO ./builder-identification.sh 2_roops $casestudy"
    bash -c "$cmd"
    if [ $? -eq 124 ]; then 
        echo ">> Execution timed out"
        break;
    fi
done

process_results_builders;
