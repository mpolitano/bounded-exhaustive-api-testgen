#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

cases="redblacktree.TreeMap doublylinkedlist.DoubleLinkedList binarysearchtree.BinarySearchTree disjointSet.orig.DisjSets disjointSet.fast.DisjSetsFast stack.list.StackLi stack.array.StackAr binaryheap.BinaryHeap"
techniques="beapi korat"
minscope=3
maxscope=4

for casestudy in $cases 
do
    for technique in $techniques 
    do
        cmd="timeout $TO ./run-begen-benchmarks-serialize.sh 1_kiasan $casestudy $minscope $maxscope"
        bash -c "$cmd"
        if [ $? -eq 124 ]; then 
            echo ">> Execution timed out"
            break;
        fi
    done
done


process-results-inclusion.sh;
    
