# BEAPI Tool: Efficient Bounded Exhaustive Input Generation from Program APIs

`BEAPI` is an efficient approach that employs routines from the API of the software under test to perform bounded exhaustive input generation. This repository includes an artifact for `BEAPI`'s paper, cited below, including an implementation of `BEAPI` and scripts to run and replicate the experiments in the paper.

- M. Politano, V. Bengolea, F. Molina, N. Aguirre, M. Frias, P. Ponzio, *Efficient Bounded Exhaustive Input Generation from Program APIs*, accepted for publication in Fundamental Approaches to Software Engineering, FASE 2023.

Note: At this point only binaries are provided for `BEAPI`'s implementation, we plan to release `BEAPI`'s source code as open source in the coming months.

# Installing BEAPI's Artifact 

Follow the instructions in `INSTALL.md`.

# Folder structure

The `0_korat` folder contains data structures implementations source from Korat.
The `1_kiasan` folder contains data structures implementations source from Kiasan.
The `2_roops` folder contains data structures implementations source from Roops.
The `3_fajita` folder contains data structures implementations source from Fajita.
The `4_real_world` folder contains data structures implementations from real worlds like Java.Utils and Apache commons.

The `lib` folder contains neccesary libs jars for run the experiments.

The `scripts` folders contains the scripts for reproduce the results in the paper.


# Reproducing the experiments

## Running a single experiment

###RQ1

To easily run a single technique over a case study we provide the `run-testgen-benchmarks.sh` script. It takes the following arguments:
```
bash `run-testgen-benchmarks.sh <project_folder> <cases> <technique> <budget>
```

For example, to analyze `SinglyLinkedList` from 0_korat benchmark using `korat`, with a scope of `4`execute: 
```
bash run-testgen-benchmarks.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList korat 4
```
To analyze using `beapi`
```
bash run-testgen-benchmarks.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList beapi 4
```

To reproduce all the experiments for a specific bencharmark study with both techniques (korat and beapi) we provide the following scripts: 

```
bash run-testgen-benchmarks-0_korat.sh
bash run-testgen-benchmarks-1_kiasan.sh
bash run-testgen-benchmarks-2_roops.sh
bash run-testgen-benchmarks-3_fajita.sh
```

To reproduce all the experiments for all cases study, you can run the following scripts:
```
bash run-testgen-benchmarks-all.sh
```

The results are shown on the screen, and stored in CSV format in file: ```scripts/results-begen/results_testgen_benchmarks.csv ```.


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
