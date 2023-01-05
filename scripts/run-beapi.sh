#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh
source $scriptsdir/common.sh

#Must be execute identify builders
# buildersDir="$scriptsdir/config/$project/builders/"
# mkdir -p $buildersDir
# touch $buildersDir/$case
# mv $BE_EXP_SRC/tmp/$case/builders.txt $scriptsdir/config/$project/builders/$case

#BEAPI RUNNER
project=$1
class=$2
scope=$3
literals=$4
finitization=$5
buildersFile=$6

file_to_string $buildersFile "|"
buildersstr=$strres
echo $buildersstr
timelimit=3600
packagename=${class%\.*}
classname=${class##*\.}

maxheap=8g
maxBEit=$((scope + scope + scope)) # Up to XX iterations in the first stage of BE
maxsize=$((maxBEit + maxBEit + maxBEit)) # Up to XX methods in a JUnit test

bejar="$projectsdir/lib/beapi.jar"
cp=$projectsdir/$project/build/classes:../lib/korat.jar
outdir=./beapi-tests

echo ""
echo "> Executing BE"

cmd="java -Xmx$maxheap -ea -cp $bejar:$cp randoop.main.Main gentests \
--testclass=$class \
--junit-output-dir=$outdir \
--usethreads=false \
--instance-generics-integer \
--disable-contracts \
--forbid-null=false \
--timelimit=$timelimit \
--literals-level=ALL \
--literals-file=$literals \
--max-BE-iterations=$maxBEit \
--all-sequences=false \
--BEmaxsize=$maxsize \
--junit-package-name=$packagename \
--instance-object-integer \
--keep-only-builder-seqs \
--efficient-extensions \
--only-test-public-members \
--ignore-public-fields \
--canonicalizer-cfg=$finitization \
--filtering=BEALL \
--builder-methods=\"$buildersstr\""


echo "$cmd"
bash -c "$cmd"

echo ""
echo "> BE finished!"

 
