#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

clean_results_folders

./run-testgen-benchmarks-0_korat.sh
./run-testgen-benchmarks-1_kiasan.sh
./run-testgen-benchmarks-2_roops.sh
./run-testgen-benchmarks-3_fajita.sh


process_results_beapi_vs_korat;
    
