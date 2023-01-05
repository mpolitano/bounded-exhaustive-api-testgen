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

function run_beapi_inclusion() {
# Check inclusion
	beapidir=results-begen-inclusion/$project/$casestudy/beapi/matching/builders/$scopeBEAPI
	beapistrs=$beapidir/beapi-tests/objects.ser
		koratstrs=results-begen-inclusion/$project/$casestudy/korat/$scopeKORAT/korat-tests/objects.ser
		config=properties/scope$scopeBEAPI.all.canonicalizer.properties
		reslog=$beapidir/inclusion-results-$scopeKORAT.txt
		diff=$beapidir/structures-not-included-$scopeKORAT.txt
		echo "************"
		cmd="./check-inclusion.sh $project $beapistrs $koratstrs $config $diff > $reslog"
		echo ">> Executing: $cmd"
		bash -c "$cmd"
	
}

######korat###############
project="$1"
casestudy="$2"
techniques="korat beapi"
scopeBEAPI=$3
scopeKORAT=$4
run_serialize korat $scopeKORAT;  
run_serialize beapi $scopeBEAPI;  

run_beapi_inclusion;

echo "************"
echo "Report"
process-results-inclusion "beapi/matching/builders"
echo "************"
