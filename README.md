# BEAPI Tool: Efficient Bounded Exhaustive Input Generation from Program APIs

`BEAPI` is an efficient approach that employs routines from the API of the software under test to perform bounded exhaustive input generation. This repository includes an artifact for `BEAPI`'s paper, cited below, including an implementation of `BEAPI` and scripts to run and replicate the experiments in the paper.

- M. Politano, V. Bengolea, F. Molina, N. Aguirre, M. Frias, P. Ponzio, *Efficient Bounded Exhaustive Input Generation from Program APIs*, accepted for publication in Fundamental Approaches to Software Engineering, FASE 2023.

Note: At this point only binaries are provided for `BEAPI`'s implementation, we plan to release `BEAPI`'s source code as open source in the coming months.

# Installing BEAPI's Artifact 

Follow the instructions in `INSTALL.md`.

# Folder structure

The following folders contain the source code of the case studies considered in the paper:

- `0_korat/src/main/java` contains the source code of the data structures implementations for the `Korat`'s benchmark.
- `1_kiasan/src/main/java` contains the source code of the data structures implementations for the `Kiasan`'s benchmark.
- `2_roops/src/main/java` contains the source code of the data structures implementations for the `ROOPS`' benchmark.
- `3_fajita/src/main/java` contains the source code of the data structures implementations for the `FAJITA`'s benchmark.
- `4_real_world/src/main/java` contains the source code of data structures implementations from the real world, drawn from the  **java.util** and **Apache Commons Collections** libraries.

Tool's binaries:

- `lib` contains the binaries for the tools and libraries required to run the experiments as .jar files.
- `lib\BEAPI.JAR` PONER EL CORRECTO binaries for the current `BEAPI` implementation. 
- `lib\korat.jar` binaries for the last `Korat` version. 

Scripts:

- `scripts` provided scripts to facilitate the execution of `BEAPI`, and to easily reproduce the experiments in the paper.


# Reproducing the paper's experiments 

## Comparison of `BEAPI` against `Korat` in benchmarks from the literature (RQ1 in Section 4.1 of the paper)

### Running a single experiment

To easily run either `BEAPI` or `Korat` in benchmarks from the literature we provide `run-testgen-benchmarks.sh` in the `scripts` folder. First, move to the scripts folder.

```
cd scripts
```

`run-testgen-benchmarks.sh` takes the following arguments:
```
./run-testgen-benchmarks.sh <benchmark> <case study> <technique> <scope>
```
where `<benchmark>` is one of `0_korat`, `1_kiasan`, `2_roops`, `3_fajita` (i.e., the name of the folder of the corresponding benchmark); `<case study>` is one of the case studies of `<benchmark>` (see below for a description of the available cases for each benchmark);  `<technique>` is either `beapi` or `korat`; and `<scope>` is the maximum number of nodes and the number of integers (from 0 to scope-1) available for generation.

For example, to generate inputs for `SinglyLinkedList` from the `0_korat` benchmark using `BEAPI` with a scope of `4` execute: 
```
./run-testgen-benchmarks.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList beapi 4
```
In this case, the ***tests suite*** generated by `BEAPI` tool is saved. This **suite** is stored in the `beapi-tests` folder located inside the specified project. For the example given above, the tests are stored in `korat_0/beapi-tests`.


To perform generation for the same case study and the same scope using `Korat` execute:
```
./run-testgen-benchmarks.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList korat 4
```

Note: For this experiment, we do not serialize to disk the objects that `Korat` builds during generation.


The screen shows a summary of the results obtained, as well as the path to the log file that each `<technique>` throws as output. Also, the results are stored, in a more readable way, as a CSV format file (```results_testgen_benchmarks.csv```) located in ```script/results-begen``` folder.  


The information tabulated in the CSV file correspond to:

- Case study information: **project** benchmark and case study **class**
- Running **technique** (BEAPI or Korat)
- **Budget** (scope) used for input generation
- **Time** spent for input generation (In second)
- Number of **structures** generated
- Number of structures visited (**explored**) during generation
 

Besides the order of presentation, the relationship between these data and those presented in **Table 1** of **Section 4.1** of the paper for each case study (see below, list of case studies, each with its corresponding short name), is completely straightforward.

### Available case studies

- `0_korat`
  - `DoublyLinkedList`: korat.examples.doublylinkedlist.DoublyLinkedList (`DDList`)
  - `FibonacciHeap`: korat.examples.fibheap.FibonacciHeap (`FibHeap`)
  -	`BinomialHeap`: korat.examples.binheap.BinomialHeap (`BinHeap`)
  - `SearchTree`:korat.examples.searchtree.SearchTree (`BST`)
  - `SinglyLinkedList`: korat.examples.singlylinkedlist.SinglyLinkedList (`SLList`)
  - `RedBlackTree`: korat.examples.redblacktree.RedBlackTree (`RBT`)
  - `SortedList`: korat.examples.sortedlist.SortedList (`SortedList`) 

- `1_kiasan`
  - `BinarySearchTree`: binarysearchtree.BinarySearchTree (`BST`)
  - `DoubleLinkedList`: doublylinkedlist.DoubleLinkedList (`DDL`)
  - `TreeSet`: redblacktree.TreeSet(`RBT`) UBICAR LOS FUENTES DONDE CORRESPONDE con el nombre correcto
  - `DisjSetsFast`: disjointSet.fast.DisjSetsFast (`DisjSetFast`)
  - `StackLi`: stack.list.StackLi (`StackList`)
  - `BinaryHeap`: binaryheap.BinaryHeap (`BHeap`)
  - `TreeMap`: redblacktree.TreeMap (`TreeMap`)
  - `DisjSet`: disjointSet.orig.DisjSets (`DisjSet`) 
  - `StackAr`: stack.array.StackAr (`StackAr`)

- `2_roops`

  - `AvlTree`: avl.AvlTree (`AVL`)
  - `NodeCachingLinkedList`: ncl.NodeCachingLinkedList (`NCL`)
  - `BinTree`: bintree.BinTree (`BinTree`)
  - `LinkedList`: linkedlist.LinkedList (`LList`)
  - `TreeSet`: rbt.TreeSet (`RBT`)
  - `FibHeap`: fibheap.FibHeap (`FibHeap`)
  - `BinomialHeap`: bheap.BinomialHeap (`BinHeap`)


- `3_fajita`
  - `BinTree `: bintree.BinTree (`BinTree`)
  - `AvlTree`: avl.AvlTree (`AVL`)
  - `TreeSet`: rbt.TreeSet (`RBT`)
  - `BinomialHeap`: bheap.BinomialHeap (`BinHeap`)
  - `SinglyLinkedList`: list.SinglyLinkedList (`SLList`) 
  - `DoubleLinkedList`: cdlist.LinkedList (`DLList`)
  - `NodeCachingLinkedList`: cList.NodeCachingLinkedList (`NCL`)

Note: The text that is inside parentheses in each case, corresponds to the short names used in **Table 1** of **Section 4.1** of the paper, to identify each case study. Furthemore, it is worth mentioning that some of the case studies may not be present in the aforementioned table of the paper (space reasons) but in replication package that accompanies the paper.

### Running all experiments from a single benchmark (slow)

To reproduce all the experiments for a specific benchrmark study with both techniques (korat and beapi) and for all scopes within XXX and YYY COMPLETAR! pick and run one of following commands: 

```
./run-testgen-benchmarks-0_korat.sh
./run-testgen-benchmarks-1_kiasan.sh
./run-testgen-benchmarks-2_roops.sh
./run-testgen-benchmarks-3_fajita.sh
```

Note: Running one of the above scripts might take a day or longer depending on your hardware

### Running all the experiments (very slow)

To reproduce all the experiments for this research question run:
```
./run-testgen-benchmarks-all.sh
```

Note: Running this script might take a few days or longer depending on your hardware

## Assessing the impact of `BEAPI`'s optimizations (RQ2 in Section 4.2 of the paper)

In this section, we assess the impact of `BEAPI`'s optimizations in its performance. We provide four different ways to execute `BEAPI`: DEFAULT (SM/BLD in the paper) is `BEAPI` with state matching enabled (SM) and using identified builders (BLD); SM is `BEAPI` with only state matching (SM) enabled; BLD is `BEAPI` using identified builders (BLD); and NoOpt is `BEAPI` with both optimizations disabled. 

### Running a single experiment

To generate inputs using `BEAPI` with a given configuration run the following script:

```
./run-testgen-beapi-optimizations.sh <benchmark> <case study> <scope> <config>
```

where `<benchmark>` is one of `0_korat`, `1_kiasan`, `2_roops`, `3_fajita`, `4_real_world`; `<case study>` is one of the case studies of `<benchmark>` (see below for the available cases for each benchmark); `<scope>` is the maximum number of nodes and the number of integers (from 0 to scope-1) available for generation, and `<config>` is one of the four aformentioned `BEAPI` configurations: `DEFAULT`, `SM`, `BLD`, `NoOpt`.

For example, to generate inputs for `SinglyLinkedList` from the `0_korat` benchmark using `BEAPI`'s DEFAULT configuration with a scope of `4` execute: 
```
./run-testgen-beapi-optimizations.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList 4 DEFAULT

```

The  **tests suite** generated by `BEAPI` is stored in the `beapi-tests` folder, located inside the specified project. For the example given above, the tests are stored in `korat_0/beapi-tests`. 


The screen shows a summary of the results obtained, as well as the path to the log file that `BEAPI` throws as output when running on the specified configuration. Also, the results are stored, in a more readable way, as a CSV format file (```results_optimizations.csv```) located in ```script/results-optimizations``` folder.  


The information tabulated in the CSV file correspond to:

- Case study information: **Project** benchmark and case study **Class**
- Running **Technique** Configuration (See below for a description)
- **Budget** (scope) used for input generation
- **Time** spent for input generation (In millisecond)
- Number of **Structures** generated
- Number of structures visited (**Explored**) during generation
 
Regarding **Technique Configurations**, the description corresponds to:

- `beapi/matching/builders` &rarr;  `DEFAULT` configuration
- `beapi/matching/no-builders` &rarr;  `SM` configuration  
- `beapi/no-matching/builders` &rarr;  `BLD` configuration
- `beapi/no-matching/no-builders` &rarr;  `NoOpt` configuration 

The data stored in this CSV file corresponds to that displayed in **Table 2** of **Section 4.2** of the paper. This paper table only shows, for certain scopes (**s**), the times spent on generation for each configuration, for the case studies mentioned in the section below. It is important to note that the times in the paper table are shown in seconds, while in the CSV report they are displayed in milliseconds.  Finally, when the CSV report does not show data for a certain case study, it means that  the time limit has been  exceeded (timeout set to 1 hour).


### Available case studies

- `0_korat`
  - `DoublyLinkedList`: korat.examples.doublylinkedlist.DoublyLinkedList (`DDList`)
  - `FibonacciHeap`: korat.examples.fibheap.FibonacciHeap (`FibHeap`)
  -	`BinomialHeap`: korat.examples.binheap.BinomialHeap (`BinHeap`)
  - `SearchTree`:korat.examples.searchtree.SearchTree (`BST`)
  - `SinglyLinkedList`: korat.examples.singlylinkedlist.SinglyLinkedList (`SLList`)
  - `RedBlackTree`: korat.examples.redblacktree.RedBlackTree (`RBT`)
  - `SortedList`: korat.examples.sortedlist.SortedList (`SortedList`) 

- `1_kiasan`
  - `BinarySearchTree`: binarysearchtree.BinarySearchTree (`BST`)
  - `DoubleLinkedList`: doublylinkedlist.DoubleLinkedList (`DDL`)
  - `TreeSet`: redblacktree.TreeSet(`RBT`) UBICAR LOS FUENTES DONDE CORRESPONDE con el nombre correcto
  - `DisjSetsFast`: disjointSet.fast.DisjSetsFast (`DisjSetFast`)
  - `StackLi`: stack.list.StackLi (`StackList`)
  - `BinaryHeap`: binaryheap.BinaryHeap (`BHeap`)
  - `TreeMap`: redblacktree.TreeMap (`TreeMap`)
  - `DisjSet`: disjointSet.orig.DisjSets (`DisjSet`) 
  - `StackAr`: stack.array.StackAr (`StackAr`)

- `2_roops`

  - `AvlTree`: avl.AvlTree (`AVL`)
  - `NodeCachingLinkedList`: ncl.NodeCachingLinkedList (`NCL`)
  - `BinTree`: bintree.BinTree (`BinTree`)
  - `LinkedList`: linkedlist.LinkedList (`LList`)
  - `TreeSet`: rbt.TreeSet (`RBT`)
  - `FibHeap`: fibheap.FibHeap (`FibHeap`)
  - `BinomialHeap`: bheap.BinomialHeap (`BinHeap`)


- `3_fajita`
  - `BinTree`: bintree1.BinTree (`BinTree`)
  - `AvlTree`: avl1.AvlTree (`AVL`)
  - `TreeSet`: rbt.TreeSet (`RBT`)
  - `BinomialHeap`: bheap.BinomialHeap (`BinHeap`)
  - `SinglyLinkedList`: list.SinglyLinkedList (`SLList`) 
  - `DoubleLinkedList`: cdlist.LinkedList (`DLList`)
  - `NodeCachingLinkedList`: cList.NodeCachingLinkedList (`NCL`)

- `4_real_world`
 
  - `NodeCachingLinkedList `: org.apache.commons.collections4.list.NodeCachingLinkedList (`NCL`)
  - `TreeSet`: java2.util2.treeset.TreeSet (`TSet`)
  - `TreeMap`: java2.util2.treemap.TreeMap (`TMap`)
  - `LinkedList`: java2.util2.linkedlist.LinkedList (`LList`)
  - `HashMap`: java2.util2.hashmap.HashMap (`HMap`)
  - `Schedule`: builders.Schedule (`Schedule`)  


Note: The text that is inside parentheses in each case, corresponds to the short names used in **Table 2** of **Section 4.2** of the paper, to identify each case study. For space reasons, the aforementioned paper table shows only results from the `2_roops` and `4_real-world` benchmarks, while the others were included in the replication package that accompanies the paper.


### Running all experiments from a single benchmark (slow)

To reproduce all the experiments for a specific benchmark using all of `BEAPI` configurations, for all scopes within XXX and YYY COMPLETAR! pick and run one of following commands: 

```
./run-testgen-beapi-optimizations-0_korat.sh
./run-testgen-beapi-optimizations-1_kiasan.sh
./run-testgen-beapi-optimizations-2_roops.sh
./run-testgen-beapi-optimizations-3_fajita.sh
./run-testgen-beapi-optimizations-real-world.sh
```

Note: Running one of the above scripts might take a day or longer depending on your hardware

### Running all the experiments (very slow)

To reproduce all the experiments for this research question run:
```
./run-testgen-beapi-optimizations-all.sh
```

Note: Running this script might take a few days or longer depending on your hardware



## Running automated builders identification (Last paragraph of Section 4.2)

In this section, we assess the cost of builder identification. For space reasons the result of builder identification are not show in the paper but on the paper website.

### Running a single experiment

To identify builders methods for a given  case study, run the following script:

```
./run-builder-identification.sh <benchmark> <case study>
```
where `<benchmark>` is one of `0_korat`, `1_kiasan`, `2_roops`, `3_fajita`, `4_real_world`; and `<case study>` is one of the case studies of `<benchmark>` ( The list of case studies is the same as the `Available case studies` section for previous  section ([Available case studies](#available-case-studies))

## Analysis of Specification using `BEAPI` (RQ3 in Section 4.3 of the paper)

In this section..., COMPLETAR!

### Running a single experiment

COMPLETAR!

### Available case studies

- `0_korat`
  - `SinglyLinkedList`: korat.examples.singlylinkedlist.SinglyLinkedList
  - XXX
  ...
- `1_kiasan`
  -
  -
...
COMPLETAR!!


### Running all experiments from a single benchmark (slow)

To reproduce all the experiments for a specific benchmark ... COMPLETAR

### Running all the experiments (very slow)

To reproduce all the experiments for this research question run:

COMPLETAR
Note: Running this script might take a few days or longer depending on your hardware



# Running `BEAPI` on your own case study

COMPLETAR!


