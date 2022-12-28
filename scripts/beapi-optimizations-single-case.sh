#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

clean_results_folders
#To run a single case
projects="$1"
cases="$2"
techniques="$3"
budgets="$4"
run_SM_BLD ; run_SM ; run_BLD ; run_No_Opt ;
process_results_optimizations;

