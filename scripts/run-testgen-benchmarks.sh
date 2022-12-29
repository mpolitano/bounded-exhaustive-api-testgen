#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

#To run a single case
project="$1"
case="$2"
technique="$3"
budget="$4"
TO=60m

cmd="timeout $TO ./run-begen-experiment.sh $project $case $technique $budget graph builders"
echo "************"
echo ">> Executing: $cmd"
bash -c "$cmd"
if [ $? -eq 124 ]; then 
    echo ">> Execution timed out"
    break;
fi

process_results_beapi_vs_korat;

