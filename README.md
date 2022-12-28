# Efficient Bounded Exhaustive Input Generation from Program APIs
# BEAPI

`BEAPI` is an efficient approach that employs routines from the API of the software under test to perform BE input generation. This repository includes the `BEAPI` artifact for the paper "Efficient Bounded Exhaustive Input Generation from Program APIs", accepted for publication in FASE 2023.

# Requirements

- Java 1.8
- Ant
- Must set environment variable BE_EXP_SRC to the current directory before running the experiments. For example: 
```export BE_EXP_SRC=$(pwd)```

# Getting Started

Clone the repository:

Move to the recently created folder:
```
cd bounded-exhaustive-api-testgen
```

# Install

....

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

To easily run a single technique over a case study we provide the `beapi-vs-korat-single-case.sh` script. It takes the following arguments:
```
bash beapi-vs-korat-single-case.sh <project_folder> <cases> <technique> <budget>
```

For example, to analyze `SinglyLinkedList`'s using `korat`, with a scope of `5`execute: 
```
bash beapi-vs-korat-single-case.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList korat 4
```
To analyze using `beapi`
```
bash beapi-vs-korat-single-case.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList beapi 4
```

The results are shown on the screen, and stored in CSV format in file: ```scripts/results-begen/results_beapi_vs_korat.csv ```.

To reproduce all the experiments for a specific bencharmark study with both techniques (korat and beapi) we provide the following scripts: 

```
bash beapi-vs-korat.sh 0_korat
```

......
.....
###RQ2

We run four different configurations of BEAPI in all case studies for increasingly large scopes. We call SM/BLD to BEAPI with state matching (SM) and builder identification (BLD) enabled; SM to BEAPI with only state matching (SM) enabled ; BLD to BEAPI with only builders (BLD) identification enabled; NoOPT has both optimizations disabled. 
To run a one case study with 4 optimizations, we provide the `beapi-optimizations-single-case.sh` script. It takes the following arguments:

```
bash beapi-optimizations-single-case.sh <project_folder> <cases> <technique> <budget>
```

For example, to analyze `SinglyLinkedList`'s using all optimizations for `beapi`, with a scope of `3`execute: 
```
bash beapi-optimizations-single-case.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList beapi 3
```

The results are shown on the screen, and stored in CSV format in file: ```scripts/results-begen/results_optimizations.csv ```.

To reproduce all the optimizations for a specific bencharmark study we provide the following scripts: 

```
bash beapi-optimizations.sh 0_korat
```
