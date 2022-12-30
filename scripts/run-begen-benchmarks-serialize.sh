#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/common.sh


TO=60m

function run_serialize() {
for technique in $techniques; do
	for ((budget=$minscope;budget<=$maxscope;budget++)); do
	cmd="timeout $TO ./run-begen-serialize-experiment.sh $project $casestudy $technique $budget graph builders"
	echo "************"
	echo ">> Executing: $cmd"
	bash -c "$cmd"
	if [ $? -eq 124 ]; then
		echo ">> Execution timed out"
	break;
	fi
	done
done
}

function run_korat_inclusion() {
# Check inclusion
for ((budget=$minscope;budget<=$maxscope;budget++)); do
	koratdir=results-begen-serialize/$project/$casestudy/korat/$budget
	koratstrs=$koratdir/korat-tests/objects.ser
	for ((inclbudget=$budget;inclbudget<=$maxscope;inclbudget++)); do
		bestrs=results-begen-serialize/$project/$casestudy/beapi/graph/builders/$inclbudget/beapi-tests/objects.ser
		config=properties/scope$budget.all.canonicalizer.properties
		reslog=$koratdir/inclusion-results-$inclbudget.txt
		diff=$koratdir/structures-not-included-$inclbudget.txt
		echo "************"
		cmd="./check-inclusion.sh $project $koratstrs $bestrs $config $diff > $reslog"
		echo ">> Executing: $cmd"
		bash -c "$cmd"
	done
done
}

function run_beapi_inclusion() {
# Check inclusion
for ((budget=$minscope;budget<=$maxscope;budget++)); do
	beapidir=results-begen-serialize/$project/$casestudy/beapi/graph/builders/$budget
	beapistrs=$beapidir/beapi-tests/objects.ser
	for ((inclbudget=$budget;inclbudget<=$maxscope;inclbudget++)); do
		koratstrs=results-begen-serialize/$project/$casestudy/korat/$inclbudget/korat-tests/objects.ser
		config=properties/scope$budget.all.canonicalizer.properties
		reslog=$beapidir/inclusion-results-$inclbudget.txt
		diff=$beapidir/structures-not-included-$inclbudget.txt
		echo "************"
		cmd="./check-inclusion.sh $project $beapistrs $koratstrs $config $diff > $reslog"
		echo ">> Executing: $cmd"
		bash -c "$cmd"
	done
done
}

######korat###############
project="$1"
casestudy="$2"
techniques="beapi korat"
minscope=$3
# maxscope=13
maxscope=$4
run_serialize ;  
run_korat_inclusion ; run_beapi_inclusion

######korat###############
# project="0_korat"
# # casestudy="korat.examples.redblacktree.RedBlackTree"
# casestudy="korat.examples.singlylinkedlist.SinglyLinkedList"

# techniques="beapi korat"
# minscope=3
# # maxscope=13
# maxscope=6

# run_many ;  
# run_korat_inclusion ; run_beapi_inclusion

# project="0_korat"
# casestudy="korat.examples.binheap.BinomialHeap"
# techniques="beapi korat"
# minscope=3
# maxscope=8
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="0_korat"
# casestudy="korat.examples.doublylinkedlist.DoublyLinkedList"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="0_korat"
# casestudy="korat.examples.searchtree.SearchTree"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="0_korat"
# casestudy="korat.examples.singlylinkedlist.SinglyLinkedList"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="0_korat"
# casestudy="korat.examples.fibheap.FibonacciHeap"
# techniques="beapi korat"
# minscope=3
# maxscope=7
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="0_korat"
# casestudy="korat.examples.sortedlist.SortedList"
# techniques="beapi korat"
# minscope=3
# maxscope=9
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="0_korat"
# casestudy="korat.examples.disjset.DisjSet"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# ##run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="0_korat"
# casestudy="korat.examples.heaparray.HeapArray"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# ##run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="0_korat"
# casestudy="korat.examples.dag.DAG"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# ##run_many ; run_korat_inclusion ; run_beapi_inclusion


# #########KIASAN#######

# project="7_kiasan"
# casestudy="redblacktree.TreeMap"
# techniques="beapi korat"
# minscope=3
# maxscope=6
# run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="7_kiasan"
# casestudy="binarysearchtree.BinarySearchTree"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="7_kiasan"
# casestudy="doublelinkedlist.DoubleLinkedList"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="7_kiasan"
# casestudy="disjointSet.orig.DisjSets"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="7_kiasan"
# casestudy="disjointSet.fast.DisjSetsFast"
# techniques="beapi korat"
# minscope=3
# maxscope=9
# run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="7_kiasan"
# casestudy="stack.list.StackLi"
# techniques="beapi korat"
# minscope=3
# maxscope=9
# run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="7_kiasan"
# casestudy="stack.array.StackAr"
# techniques="beapi korat"
# minscope=3
# maxscope=8
# run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="7_kiasan"
# casestudy="binaryHeap.BinaryHeap"
# techniques="beapi korat"
# minscope=3
# maxscope=9
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# #########ROOPS##########


# project="8_roops"
# casestudy="fibheap.FibHeap"
# techniques="beapi korat"
# minscope=3
# maxscope=5
# run_many ; run_korat_inclusion ; run_beapi_inclusion



# project="8_roops"
# casestudy="bintree.BinTree"
# techniques="beapi korat"
# minscope=3
# maxscope=4
# run_many ; run_korat_inclusion ; run_beapi_inclusion



# project="8_roops"
# casestudy="rbt.TreeSet"
# techniques="beapi korat"
# minscope=3
# maxscope=13
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="8_roops"
# casestudy="avl.AvlTree"
# techniques="beapi korat"
# minscope=3
# maxscope=6
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="8_roops"
# casestudy="bheap.BinomialHeap"
# techniques="beapi korat"
# minscope=3
# maxscope=8
# run_many ; run_korat_inclusion ; run_beapi_inclusion



# project="8_roops"
# casestudy="ncl.NodeCachingLinkedList"
# techniques="beapi korat"
# minscope=3
# maxscope=7
# run_many ; run_korat_inclusion ; run_beapi_inclusion



# project="8_roops"
# casestudy="linkedlist.LinkedList"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="8_roops"
# casestudy="singlelist.SinglyLinkedList"
# techniques="beapi korat"
# minscope=3
# maxscope=10
# run_many ; run_korat_inclusion ; run_beapi_inclusion



# ############FAJITA###########

# project="9_fajita"
# casestudy="rbt.TreeSet"
# techniques="beapi korat"
# minscope=3
# maxscope=13
# run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="9_fajita"
# casestudy="rbtkiasan.TreeSet"
# techniques="beapi korat"
# minscope=3
# maxscope=8
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="9_fajita"
# casestudy="avl1.AvlTree"
# techniques="beapi korat"
# minscope=3
# maxscope=11
# run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="9_fajita"
# casestudy="avlfix.AvlTree"
# techniques="beapi korat"
# minscope=3
# maxscope=11
# run_many ; run_korat_inclusion ; run_beapi_inclusion



# project="9_fajita"
# casestudy="bheap.BinomialHeap"
# techniques="beapi korat"
# minscope=3
# maxscope=8
# run_many ; run_korat_inclusion ; run_beapi_inclusion

# project="9_fajita"
# casestudy="bheapkorat.BinomialHeap"
# techniques="beapi korat"
# minscope=3
# maxscope=8
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="9_fajita"
# casestudy="bintree1.BinTree"
# techniques="beapi korat"
# minscope=3
# maxscope=6
# run_many ; run_korat_inclusion ; run_beapi_inclusion



# project="9_fajita"
# casestudy="list.SinglyLinkedList"
# techniques="beapi korat"
# minscope=3
# maxscope=8
# run_many ; run_korat_inclusion ; run_beapi_inclusion



# project="9_fajita"
# casestudy="cdlist.LinkedList"
# techniques="beapi korat"
# minscope=3
# maxscope=7
# run_many ; run_korat_inclusion ; run_beapi_inclusion


# project="9_fajita"
# casestudy="cList.NodeCachingLinkedList"
# techniques="beapi korat"
# minscope=3
# maxscope=8
# run_many ; run_korat_inclusion ; run_beapi_inclusion


