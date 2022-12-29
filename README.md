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
- `4_real_world/src/main/java` contains the source code of data structures implementations from the real world, drawn from the  
**java.util** and **Apache Commons Collections** libraries.

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



ACA HAY QUE ACLARAR SI ESTO GENERA TESTS/OBJETOS O AMBOS, Y DONDE ESTA CADA OUTPUT

To perform generation for the same case study and the same scope using `Korat` execute:
```
./run-testgen-benchmarks.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList korat 4
```

ACA HAY QUE ACLARAR DONDE DEJA KORAT LOS OBJETOS


The screen shows a summary of the results obtained, as well as the path to the log file that each `<technique>` throws as[ ](url)output. Also, the results are stored in a CSV format file (```results_testgen_benchmarks.csv```) located in ```script/results-begen``` folder.  


The information tabulated in the csv file correspond to:

- Case study information: project benchmark and case study
- Running technique (BEAPI or Korat)
- Time spent for generation (In second)
- Number of structures generated
- Number of structures visited during generation
 

LINKEAR DE ALGUNA MANERA CON LA INFO QUE ESTA EN LA TABLA 1


### Available case studies

- `0_korat`
  - `DoublyLinkedList`: korat.examples.doublylinkedlist.DoublyLinkedList (`DDList`)
  - `FibonacciHeap`: korat.examples.fibheap.FibonacciHeap (`FibHeap`)
  -	`BinomialHeap`: korat.examples.binheap.BinomialHeap (`BinHeap`)
  - `SearchTree`:korat.examples.searchtree.SearchTree (`BST`)
  - `SinglyLinkedList`: korat.examples.singlylinkedlist.SinglyLinkedList (`SLList`)
  - `RedBlackTree`: korat.examples.redblacktree.RedBlackTree (`RBT`)

- `1_kiasan`
  - `BinarySearchTree`: binarysearchtree.BinarySearchTree (`BST`)
  - `DoubleLinkedList`: doublylinkedlist.DoubleLinkedList (`DDL`)
  - `DisjSetsFast`: disjointSet.fast.DisjSetsFast (`DisjSetFast`)
  - `StackLi`: stack.list.StackLi (`StackList`)
  - `BinaryHeap`: binaryheap.BinaryHeap (`BHeap`)
  - `TreeMap`: redblacktree.TreeMap (`TreeMap`)	

- `2_roops`

  - `AvlTree`: avl.AvlTree (`AVL`)
  - `NodeCachingLinkedList`: ncl.NodeCachingLinkedList (`NCL`)
  - `BinTree`: bintree.BinTree (`BinTree`)
  - `LinkedList`: linkedlist.LinkedList (`LList`)
  - `TreeSet`: rbt.TreeSet (`RBT`)
  - `FibHeap`: fibheap.FibHeap (`FibHeap`)
  - `BinomialHeap`: bheap.BinomialHeap (`BinHeap`)

COMPLETAR!

Note: COMPLETAR

### Running all experiments from a single benchmark (slow)

To reproduce all the experiments for a specific bencharmark study with both techniques (korat and beapi) and for all scopes within XXX and YYY COMPLETAR! pick and run one of following commands: 

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

FALTA DECIR SI ESTO GENERA SUITES/OBJETOS, Y DONDE SE GUARDAN

FALTA EXPLICAR COMO LEER EL OUTPUT, Y COMO SE RELACIONA CON LOS DATOS EN LAS TABLAS CORRESPONDIENTES DEL PAPER

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

COMPLETAR!



# Running `BEAPI` on your own case study

COMPLETAR!


