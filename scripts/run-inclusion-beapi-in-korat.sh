#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/common.sh
source $scriptsdir/process-results.sh


TO=60m

function run_serialize() {
for technique in $techniques; do
	for ((budget=$scopeMin;budget<=$scopeMax;budget++)); do
	cmd="timeout $TO ./run-begen-serialize-experiment.sh $project $casestudy $technique $budget matching builders"
	echo "************"
	echo ">> Executing: $cmd"
	bash -c "$cmd"
	if [ $? -eq 124 ]; then
		echo ">> Execution timed out"
	break;
	fi
	done
done
}

function run_beapi_inclusion() {
# Check inclusion
for ((budget=$scopeMin;budget<=$scopeMax;budget++)); do
	beapidir=results-begen-inclusion/$project/$casestudy/beapi/matching/builders/$budget
	beapistrs=$beapidir/beapi-tests/objects.ser
	for ((inclbudget=$budget;inclbudget<=$scopeMax;inclbudget++)); do
		koratstrs=results-begen-inclusion/$project/$casestudy/korat/$inclbudget/korat-tests/objects.ser
		config=properties/scope$budget.all.canonicalizer.properties
		reslog=$beapidir/inclusion-results-$inclbudget.txt
		diff=$beapidir/structures-not-included-$inclbudget.txt
		echo "************"
		cmd="./check-inclusion.sh $project $beapistrs $koratstrs $config $diff > $reslog"
		echo ">> Executing: $cmd"
		bash -c "$cmd"
	done
done
}

######korat###############
project="$1"
casestudy="$2"
techniques="korat beapi"
scopeMin=$3
scopeMax=$4
run_serialize;  
run_beapi_inclusion;
process-results-inclusion "beapi/matching/builders"