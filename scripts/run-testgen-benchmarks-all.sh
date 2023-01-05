#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

clean_results_folders

./run-testgen-benchmarks-0_korat.sh $budgetMax
./run-testgen-benchmarks-1_kiasan.sh $budgetMax
./run-testgen-benchmarks-2_roops.sh $budgetMax
./run-testgen-benchmarks-3_fajita.sh $budgetMax
    
