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
    resultsdir=$scriptsdir/results-begen-inclusion/$project/$class/$technique/$opt1/$opt2/$scope/
else
    resultsdir=$scriptsdir/results-begen-inclusion/$project/$class/$technique/$scope/
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

# Create serial output folder
outdir=./$technique-tests
if [[ -d $outdir ]]; then
    rm -rf $outdir
fi
mkdir -p $outdir

cmd="$scriptsdir/gen-$technique-serialize-inputs.sh $project $class $scope $opt1 $opt2 > $explog"
echo ""
echo "> Generating tests: $cmd"
bash -c "$cmd" 

cmd="cp -r $projectdir/$technique-tests $resultsdir"
echo ""
echo "> Saving tests: $cmd"
bash -c "$cmd" 

popd > /dev/null

echo ""
echo "> Experiment finished! Results in: $resultsdir"

