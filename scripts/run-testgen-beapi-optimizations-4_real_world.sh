#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

cases="java2.util2.linkedlist.LinkedList java2.util2.treemap.TreeMap java2.util2.treeset.TreeSet java2.util2.hashmap.HashMap builders.Schedule org.apache.commons.collections4.list.NodeCachingLinkedList"
budgetMax="$1"

config="DEFAULT SM BLD NoOpt"
for optimization in $config 
do
	for casestudy in $cases 
	do
	    for budget in $(seq 3 $budgetMax)
	    do
	        cmd="timeout $TO ./run-testgen-beapi-optimizations.sh 4_real_world $casestudy $budget $optimization"
	        bash -c "$cmd"
	        if [ $? -eq 124 ]; then 
	            echo ">> Execution timed out"
	            break;
	        fi
	    done
	done
done
