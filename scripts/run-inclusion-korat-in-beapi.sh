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

function run_korat_inclusion() {
# Check inclusion
for ((budget=$scopeMin;budget<=$scopeMax;budget++)); do
	koratdir=results-begen-inclusion/$project/$casestudy/korat/$budget
	koratstrs=$koratdir/korat-tests/objects.ser
	for ((inclbudget=$budget;inclbudget<=$scopeMax;inclbudget++)); do
		bestrs=results-begen-inclusion/$project/$casestudy/beapi/matching/builders/$inclbudget/beapi-tests/objects.ser
		config=properties/scope$budget.all.canonicalizer.properties
		reslog=$koratdir/inclusion-results-$inclbudget.txt
		diff=$koratdir/structures-not-included-$inclbudget.txt
		echo "************"
		cmd="./check-inclusion.sh $project $koratstrs $bestrs $config $diff > $reslog"
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
run_korat_inclusion;
process-results-inclusion "korat"