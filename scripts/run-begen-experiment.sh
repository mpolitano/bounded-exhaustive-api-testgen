#!/bin/bash
projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/common.sh
project=$1
class=$2
# must be one of: korat | beapi
technique=$3
scope=$4
opt1=$5
opt2=$6

projectdir=$projectsdir/$project
if [[ $technique == "beapi"* ]]; then
    resultsdir=$scriptsdir/results-begen/$project/$class/$technique/$opt1/$opt2/$scope/
else
    resultsdir=$scriptsdir/results-begen/$project/$class/$technique/$scope/
fi
if [[ -d $resultsdir ]]; then
    rm -rf $resultsdir
fi
mkdir -p $resultsdir
explog=$resultsdir/log.txt

pushd $projectdir > /dev/null

echo ""
echo "> Starting experiment: $@"

clean_and_compile

cmd="$scriptsdir/gen-$technique-inputs.sh $project $class $scope $opt1 $opt2 > $explog"
echo ""
echo "> Generating tests: $cmd"
bash -c "$cmd" 

popd > /dev/null

echo ""
echo "> Experiment finished! Results in: $resultsdir"

