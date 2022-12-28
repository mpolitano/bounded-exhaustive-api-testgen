#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

#To run one package
projects="$1"
echo "$projects"
if [[ $projects == "0_korat" ]]; then 
	echo "aca"
    cases="korat.examples.singlylinkedlist.SinglyLinkedList korat.examples.binheap.BinomialHeap korat.examples.redblacktree.RedBlackTree korat.examples.doublylinkedlist.DoublyLinkedList korat.examples.searchtree.SearchTree korat.examples.fibheap.FibonacciHeap"
fi
if [[ $projects == "3_fajita" ]]; then 
    cases="bheapkorat.BinomialHeap bheap.BinomialHeap avlfix.AvlTree avl1.AvlTree rbt.TreeSet rbtkiasan.TreeSet bintree1.BinTree list.SinglyLinkedList cdlist.LinkedList cList.NodeCachingLinkedList"
fi
if [[ $projects == "2_roops" ]]; then 
    cases="fibheap.FibHeap rbt.TreeMapeSet bheap.BinomialHeap avl.AvlTree linkedlist.LinkedList singlelist.SinglyLinkedList bintree.BinTree ncl.NodeCachingLinkedList"
fi
if [[ $projects == "1_kiasan" ]]; then 
    cases="redblacktree.TreeMap doublelinkedlist.DoubleLinkedList binarysearchtree.BinarySearchTree disjointSet.orig.DisjSets disjointSet.fast.DisjSetsFast stack.list.StackLi stack.array.StackAr binaryheap.BinaryHeap"
fi

budgets="3 4 5"
techniques="beapi korat"
run_beapi_korat;
process_results_beapi_vs_korat;