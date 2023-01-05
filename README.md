# BEAPI Tool: Efficient Bounded Exhaustive Input Generation from Program APIs

`BEAPI` is an efficient bounded exhaustive test generation approach that employs routines from the API of the software under test for generation. This repository includes an artifact for `BEAPI`'s paper, cited below, including the current implementation of `BEAPI` and scripts to run and replicate the experiments in the paper.

- M. Politano, V. Bengolea, F. Molina, N. Aguirre, M. Frias, P. Ponzio, *Efficient Bounded Exhaustive Input Generation from Program APIs*, accepted for publication in Fundamental Approaches to Software Engineering, FASE 2023.

Note: At this point only binaries are provided for `BEAPI`'s implementation, we plan to release `BEAPI`'s source code as open source in the coming months.

# Installing BEAPI's Artifact 

Follow the instructions in [INSTALL.md](INSTALL.md).

# Folder structure

The following folders contain the source code of the case studies considered in the paper:

- `0_korat/src/main/java`: contains the source code of the data structures implementations for the `Korat`'s benchmark.
- `1_kiasan/src/main/java`: contains the source code of the data structures implementations for the `Kiasan`'s benchmark.
- `2_roops/src/main/java`: contains the source code of the data structures implementations for the `ROOPS`' benchmark.
- `3_fajita/src/main/java`: contains the source code of the data structures implementations for the `FAJITA`'s benchmark.
- `4_real_world/src/main/java`: contains the source code of data structures implementations from the real world, drawn from the  **java.util** and **Apache Commons Collections** libraries.

Tool's binaries:

- `lib`: contains the binaries for the tools and libraries required to run the experiments as .jar files.
- `lib\BEAPI.JAR`: PONER EL CORRECTO CACHO binaries for the current `BEAPI` implementation. 
- `lib\korat.jar`: binaries for the last `Korat` version. 

Scripts:

- `scripts`: provided scripts to facilitate the execution of `BEAPI`, and to easily reproduce the experiments in the paper.


# Reproducing the paper's experiments 

### Comparison of `BEAPI` against `Korat` in benchmarks from the literature (RQ1 in Section 4.1 of the paper)

For instructions on reproducing this set of experiments click [here](BEAPI_v_KORAT.md).

### Assessing the impact of `BEAPI`'s optimizations (RQ2 in Section 4.2 of the paper)

For instructions on reproducing this set of experiments click [here](BEAPI_OPT.md).

### Analysis of Specifications using `BEAPI` (RQ3 in Section 4.3 of the paper)

For instructions on reproducing this set of experiments click [here](BEAPI_SPECS.md).

# Running `BEAPI` on your own case study

For instructions on running `BEAPI` on your preferred case study click [here](RUN_BEAPI.md).



