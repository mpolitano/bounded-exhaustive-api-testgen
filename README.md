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
bash run-testgen-benchmarks.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList beapi 4
```

To perform generation for the same case study and the same scope using `Korat` execute:
```
bash run-testgen-benchmarks.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList korat 4
```

The results are shown on the screen, and stored in CSV format in file: ```scripts/results-begen/results_testgen_benchmarks.csv ```. NO SE ENTIENDE. Hay que poner qué resultados hay en el CSV y explicarlos brevemente.


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

### Running all the experiments for a single benchmark (slow)

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

###RQ2

We run four different configurations of BEAPI in all case studies for increasingly large scopes. We call SM/BLD to BEAPI with state matching (SM) and builder identification (BLD) enabled; SM to BEAPI with only state matching (SM) enabled ; BLD to BEAPI with only builders (BLD) identification enabled; NoOPT has both optimizations disabled. 

To run a one case study with 4 optimizations, we provide the `beapi-optimizations.sh` script. It takes the following arguments:

```
bash beapi-optimizations.sh <project_folder> <case> <budget>
```

For example, to analyze `SinglyLinkedList`'s using all optimizations for `beapi`, with a scope of `3`execute: 
```
bash beapi-optimizations.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList 3
```

To reproduce all the optimizations for a specific bencharmark study we provide the following scripts: 

```
bash beapi-optimizations.sh 0_korat
```
```
bash beapi-optimizations-0_korat.sh
bash beapi-optimizations-1_kiasan.sh
bash beapi-optimizations-2_roops.sh
bash beapi-optimizations-3_fajita.sh
bash beapi-optimizations-real-world.sh

```

For run with with all cases studies you must be run:
```
bash beapi-optimizations-all.sh
```
