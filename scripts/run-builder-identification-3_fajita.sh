#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="bheap.BinomialHeap avl.AvlTree rbt.TreeSet bintree.BinTree list.SinglyLinkedList cdlist.LinkedList cList.NodeCachingLinkedList"

for casestudy in $cases 
do
    cmd="timeout $TO ./run-builder-identification.sh 3_fajita $casestudy"
    bash -c "$cmd"
    if [ $? -eq 124 ]; then 
        echo ">> Execution timed out"
        break;
    fi
done

