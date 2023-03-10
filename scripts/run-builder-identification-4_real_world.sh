#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="java2.util2.linkedlist.LinkedList java2.util2.treemap.TreeMap java2.util2.treeset.TreeSet java2.util2.hashmap.HashMap org.apache.commons.collections4.list.NodeCachingLinkedList"


for casestudy in $cases 
do
    cmd="timeout $TO ./run-builder-identification.sh 4_real_world $casestudy"
    bash -c "$cmd"
    if [ $? -eq 124 ]; then 
        echo ">> Execution timed out"
        break;
    fi
done
