#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/process-results.sh
source $scriptsdir/common.sh
maxheap=$BE_EXP_MAXHEAP

# Example invocation:
#./check-inclusion.sh 8_roops results-begen/8_roops/rbt.TreeSet/korat/3/korat-tests/objects.ser results-begen/8_roops/rbt.TreeSet/beapi/graph/builders/3/beapi-tests/objects.ser properties/scope3.all.canonicalizer.properties results-begen/8_roops/rbt.TreeSet/korat/3/structures-not-in-beapi.txt

project=$1
strs=$2
targetstrs=$3
canconfig=$4
notinclstrs=$5

projectdir=$projectsdir/$project

pushd $projectdir > /dev/null
clean_and_compile
popd > /dev/null

pushd $scriptsdir > /dev/null

cp=../$project/build/classes:../lib/structures-inclusion.jar:../lib/korat.jar

cmd="java -Xmx$maxheap -ea -cp $cp inclusion.main.CheckInclusion \"$strs\" \"$targetstrs\" \"$canconfig\" \"$notinclstrs\""
echo "> Executing: $cmd" 
bash -c "$cmd"

popd > /dev/null

