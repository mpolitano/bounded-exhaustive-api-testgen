#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

#To run a single case
project="$1"
case="$2"
budget="$3"
TO=60m

projectdir=$projectsdir/$project
pushd $projectdir > /dev/null

echo ""
echo "> Starting experiment: $@"

clean_and_compile

options_builders="builders no-builders"
options_state_matching="graph no-matching"
for opt1 in $options_state_matching 
do
    for opt2 in $options_builders 
    do  
        resultsdir=$scriptsdir/results-optimizations/$project/$case/beapi/$opt1/$opt2/$budget/
        if [[ -d $resultsdir ]]; then
            rm -rf $resultsdir
        fi  
        mkdir -p $resultsdir
        explog=$resultsdir/log.txt
        cmd="timeout $TO $scriptsdir/gen-beapi-inputs.sh $project $case $budget $opt1 $opt2 > $explog"
        echo "************"
        echo ">> Executing: $cmd"
        bash -c "$cmd"
        if [ $? -eq 124 ]; then 
            echo ">> Execution timed out"
            # break;
            break 3;
        fi
    done
done
popd
process_results_optimizations;