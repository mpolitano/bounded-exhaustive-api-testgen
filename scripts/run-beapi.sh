#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

#To run a single case
project="$1"
case="$2"
scope="$3"

explog="results-beapi/log.txt"
mkdir -p results-beapi
pushd $BE_EXP_SRC/$project
ant
popd
cmd="$scriptsdir/run-builder-identification.sh $project $case > $explog"
echo ""
echo "> Identify builders: $cmd"
bash -c "$cmd" 

buildersDir="$scriptsdir/config/$project/builders/"
mkdir -p $buildersDir
touch $buildersDir/$case
mv $BE_EXP_SRC/tmp/$case/builders.txt $scriptsdir/config/$project/builders/$case

cmd="$scriptsdir/gen-beapi-inputs.sh $project $case $scope matching builders"
echo ""
echo "> Generating tests: $cmd"
bash -c "$cmd" 
