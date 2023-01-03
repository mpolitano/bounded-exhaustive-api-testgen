#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="bheapkorat.BinomialHeap bheap.BinomialHeap avlfix.AvlTree avl1.AvlTree rbt.TreeSet rbtkiasan.TreeSet bintree1.BinTree list.SinglyLinkedList cdlist.LinkedList cList.NodeCachingLinkedList"
techniques="beapi korat"
minscope=3
maxscope=4

for casestudy in $cases 
do
    for technique in $techniques 
    do
        cmd="timeout $TO ./run-begen-benchmarks-serialize.sh 3_fajita $casestudy $minscope $maxscope"
        bash -c "$cmd"
        if [ $? -eq 124 ]; then 
            echo ">> Execution timed out"
            break;
        fi
    done
done


# process-results-inclusion.sh;
    
