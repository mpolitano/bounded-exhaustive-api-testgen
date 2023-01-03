#!/bin/bash
projectsdir=$BE_EXP_SRC

project=$1
class=$2
scope=$3

pushd $projectsdir/$project > /dev/null
outdir=./korat-tests

KORAT_CP=./build/classes/:../lib/:../lib/korat.jar
java -cp $KORAT_CP korat.Korat --class $class --args $scope --serialize $outdir/objects.ser
#--visualize \
#--printCandVects \
#--cvFile korat.csv \

popd > /dev/null

