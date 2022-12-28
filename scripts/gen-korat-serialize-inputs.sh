#!/bin/bash
projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts

project=$1
class=$2
scope=$3

pushd $projectsdir/$project > /dev/null
outdir=./korat-tests

KORAT_CP=../lib/korat.jar:./build/classes/:../lib/
java -cp $KORAT_CP korat.Korat --class $class --args $scope --serialize $outdir/objects.ser
#--visualize \
#--printCandVects \
#--cvFile korat.csv \

popd > /dev/null

