# Efficient Bounded Exhaustive Input Generation from Program APIs
# BEAPI

`BEAPI` is an efficient approach that employs routines from the API of the software under test to perform BE input generation. This repository includes the `BEAPI` artifact for the paper "Efficient Bounded Exhaustive Input Generation from Program APIs", accepted for publication in FASE 2023.

# Requirements

- Java 1.8
- Ant
- Must set environment variable BE_EXP_SRC to the current directory before running the experiments. For example: 
```export BE_EXP_SRC=$(pwd)```

# Getting Started

Clone the repository and

Move to the recently created folder
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

For example, to analyze `SinglyLinkedList`'s using `korat`, with up to a scope of `5`execute: 
```
bash beapi-vs-korat-single-case.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList 4 korat
```
To analyze using `beapi`
```
bash beapi-vs-korat-single-case.sh 0_korat korat.examples.singlylinkedlist.SinglyLinkedList 4 beapi
```

The results are shown on the screen, and stored in CSV format in file: ```scripts/results-begen/results_beapi_vs_korat.csv ```.

To reproduce all the experiments for a specific bencharmark study with both techniques (korat and beapi) we provide the following scripts: 

```
bash beapi-vs-korat.sh 0_korat
```

......
.....
###RQ2

