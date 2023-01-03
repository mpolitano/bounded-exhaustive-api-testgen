#!/bin/bash
projectsdir=$BE_EXP_SRC

project=$1
class=$2
scope=$3

pushd $projectsdir/$project > /dev/null

KORAT_CP=./build/classes/:../lib/korat.jar:../lib/
java -cp $KORAT_CP korat.Korat --class $class --args $scope
#--serialize objects.ser
#--visualize \
#--printCandVects \
#--cvFile korat.csv \

popd > /dev/null

