#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

#To run a single case
projects="$1"
cases="$2"
techniques="$3"
budgets="$4"
run_beapi_korat;
process_results_beapi_vs_korat;

