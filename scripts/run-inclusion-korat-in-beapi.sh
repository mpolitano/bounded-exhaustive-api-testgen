#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/common.sh
source $scriptsdir/process-results.sh


TO=60m

function run_serialize() {
	technique=$1
	budget=$2
	cmd="timeout $TO ./run-begen-serialize-experiment.sh $project $casestudy $technique $budget matching builders"
	echo "************"
	echo ">> Executing: $cmd"
	bash -c "$cmd"
	if [ $? -eq 124 ]; then
		echo ">> Execution timed out"
	break;
	fi
}

function run_korat_inclusion() {
# Check inclusion
	koratdir=results-begen-inclusion/$project/$casestudy/korat/$scopeKORAT
	koratstrs=$koratdir/korat-tests/objects.ser
	bestrs=results-begen-inclusion/$project/$casestudy/beapi/matching/builders/$scopeBEAPI/beapi-tests/objects.ser
	config=properties/scope$scopeKORAT.all.canonicalizer.properties
	reslog=$koratdir/inclusion-results-$scopeBEAPI.txt
	diff=$koratdir/structures-not-included-$scopeBEAPI.txt
	echo "************"
	cmd="./check-inclusion.sh $project $koratstrs $bestrs $config $diff > $reslog"
	echo ">> Executing: $cmd"
	bash -c "$cmd"

}



######korat###############
project="$1"
casestudy="$2"
scopeKORAT=$3
scopeBEAPI=$4
run_serialize korat $scopeKORAT;  
run_serialize beapi $scopeBEAPI;  
run_korat_inclusion;
process-results-inclusion "korat"