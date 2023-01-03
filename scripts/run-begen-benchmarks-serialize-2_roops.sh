#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="fibheap.FibHeap rbt.TreeSet bheap.BinomialHeap avl.AvlTree linkedlist.LinkedList singlelist.SinglyLinkedList bintree.BinTree ncl.NodeCachingLinkedList"
techniques="beapi korat"
minscope=3
maxscope=4

for casestudy in $cases 
do
    for technique in $techniques 
    do
        cmd="timeout $TO ./run-begen-benchmarks-serialize.sh 2_roops $casestudy $minscope $maxscope"
        bash -c "$cmd"
        if [ $? -eq 124 ]; then 
            echo ">> Execution timed out"
            break;
        fi
    done
done


process-results-inclusion.sh;
    
