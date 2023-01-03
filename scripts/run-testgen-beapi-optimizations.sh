#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

#To run a single case
project="$1"
case="$2"
budget="$3"
config="$4"

if [[ $config == "DEFAULT" ]]
then
    options_builders="builders"
    options_state_matching="matching"
elif [[ $config == "SM" ]]
then
    options_builders="no-builders"
    options_state_matching="matching"
elif [[ $config == "BLD" ]]
then
    options_builders="builders"
    options_state_matching="no-matching"
elif [[ $config == "NoOpt" ]]
then
    options_builders="no-builders"
    options_state_matching="no-matching" 
 else
    echo "Unknown optimization option: $config"
    exit 1
fi

TO=60m

projectdir=$projectsdir/$project
pushd $projectdir > /dev/null

echo ""
echo "> Starting experiment: $@"

clean_and_compile

resultsdir=$scriptsdir/results-optimizations/$project/$case/beapi/$options_state_matching/$options_builders/$budget/
if [[ -d $resultsdir ]]; then
    rm -rf $resultsdir
fi  
mkdir -p $resultsdir
explog=$resultsdir/log.txt
cmd="timeout $TO $scriptsdir/gen-beapi-inputs.sh $project $case $budget $options_state_matching $options_builders > $explog"
echo "************"
echo ">> Executing: $cmd"
bash -c "$cmd"
if [ $? -eq 124 ]; then 
    echo ">> Execution timed out"
    # break;
    break 3;
fi
popd

echo "************"
echo "Report"
process_results_optimizations_display $project $case  "beapi/$options_state_matching/$options_builders" $budget ;
echo "************"
