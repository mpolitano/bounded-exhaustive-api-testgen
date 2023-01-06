#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="redblacktree.TreeMap redblacktree.TreeSet doublylinkedlist.DoubleLinkedList binarysearchtree.BinarySearchTree disjointSet.orig.DisjSets disjointSet.fast.DisjSetsFast stack.list.StackLi binaryheap.BinaryHeap"


for casestudy in $cases 
do
    cmd="timeout $TO ./run-builder-identification.sh 1_kiasan $casestudy"
    bash -c "$cmd"
    if [ $? -eq 124 ]; then 
        echo ">> Execution timed out"
        break;
    fi
done
