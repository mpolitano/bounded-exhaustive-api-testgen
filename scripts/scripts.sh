#!/bin/bash
source $scriptsdir/common.sh

TO=60m

function process_results_beapi_vs_korat() {
    techniques="korat beapi/discover/builders"

    resultsdir=./results-begen/
    tmpfile="$resultsdir/results_testgen_benchmarks.csv"

    [[ -f $tmpfile ]] && rm $tmpfile
    echo "Project,Class,Technique,Budget,Time,Structures,Explored" > $tmpfile

    projects=$(ls $resultsdir)
    [[ $projects == "" ]] && echo "No proyects found in $currdir" && exit -1;
    for project in $projects
    do
        currdir=$resultsdir/$project
        cases=$(ls $currdir)
        [[ $cases == "" ]] && echo "No case studies found in $currdir" && continue;
        for casestudy in $cases 
        do
            currdir=$resultsdir/$project/$casestudy
            for technique in $techniques 
            do
                currdir=$resultsdir/$project/$casestudy/$technique
                [[ ! -d $currdir ]] && continue;
                budgets=$(ls $currdir)
                [[ $budgets == "" ]] && echo "No budgets found in $currdir" && continue;
                for budget in $budgets
                do
                    currdir=$resultsdir/$project/$casestudy/$technique/$budget/
                    [[ ! -d $currdir ]] && continue;
                    logfile=$currdir/log.txt

                    gentime=""
                    structures=""
                    explored=""

                    if [[ $technique == "korat" ]]; then
                        gentime=$(grep "Overall time" $logfile | cut -d' ' -f3)
                        structures=$(grep "New found" $logfile | cut -d':' -f2)
                        explored=$(grep "Total explored" $logfile | cut -d':' -f2)
                    else
                        gentime=$(grep "Bounded exhaustive generation time" $logfile | cut -d' ' -f5)
                        gentime=$(echo "result = (${gentime%??}/1000); scale=2; result / 1" | bc -l)
                        structures=$(grep "Number of builder sequences" $logfile | cut -d' ' -f5)
                        explored=$(grep "Number of sequences explored" $logfile | cut -d' ' -f5)
                    fi

                    echo "$project,$casestudy,$technique,$budget,$gentime,$structures,$explored" >> $tmpfile

                done
            done
        done
    done
}

function process_results_beapi_vs_korat_display() {
    
    project=$1
    casestudy=$2
    technique=$3
    budget=$4

    if [[ $technique == "beapi"* ]]; then
        resultsdir=results-begen/$project/$casestudy/$technique/discover/builders/$budget/
    else
        resultsdir=results-begen/$project/$casestudy/$technique/$budget/
    fi
    echo "Project,Class,Technique,Budget,Time,Structures,Explored"


    logfile=$resultsdir/log.txt

    gentime=""
    structures=""
    explored=""

    if [[ $technique == "korat" ]]; then
        gentime=$(grep "Overall time" $logfile | cut -d' ' -f3)
        structures=$(grep "New found" $logfile | cut -d':' -f2)
        explored=$(grep "Total explored" $logfile | cut -d':' -f2)
    else
        gentime=$(grep "Bounded exhaustive generation time" $logfile | cut -d' ' -f5)
        gentime=$(echo "result = (${gentime%??}/1000); scale=2; result / 1" | bc -l)
        structures=$(grep "Number of builder sequences" $logfile | cut -d' ' -f5)
        explored=$(grep "Number of sequences explored" $logfile | cut -d' ' -f5)
    fi

    echo "$project,$casestudy,$technique,$budget,$gentime,$structures,$explored"

}
    
function process_results_optimizations() {
    resultsdir=./results-optimizations/
    techniques="beapi/matching/builders beapi/matching/no-builders beapi/no-matching/builders beapi/no-matching/no-builders"

    tmpfile="$resultsdir/results_optimizations.csv"
    tmpfilebuilders="builders.txt"
    [[ -f $tmpfile ]] && rm $tmpfile
    [[ -f $tmpfilebuilders ]] && rm $tmpfilebuilders
    echo "Project,Class,Technique,Budget,Time,Structures,Explored" > $tmpfile
    echo $resultsdir
    projects=$(ls $resultsdir)
    [[ $projects == "" ]] && echo "No proyects found in $currdir" && exit -1;
    for project in $projects
    do
        currdir=$resultsdir/$project
        cases=$(ls $currdir)
        [[ $cases == "" ]] && echo "No case studies found in $currdir" && continue;
        for casestudy in $cases 
        do
            currdir=$resultsdir/$project/$casestudy
            for technique in $techniques 
            do
                currdir=$resultsdir/$project/$casestudy/$technique
                [[ ! -d $currdir ]] && continue;
                budgets=$(ls $currdir)

                if [[ $technique == "beapi/discover/discover" ]]; then
                    echo "$casestudy" >> $tmpfilebuilders
                    cat "$currdir/builders.txt" >> $tmpfilebuilders
                fi

                [[ $budgets == "" ]] && echo "No budgets found in $currdir" && continue;
                for budget in $budgets
                do
                    currdir=$resultsdir/$project/$casestudy/$technique/$budget/
                    [[ ! -d $currdir ]] && continue;
                    logfile=$currdir/log.txt

                    gentime=""
                    structures=""
                    explored=""

                    gentime=$(grep "Bounded exhaustive generation time" $logfile | cut -d' ' -f5)
                    # gentime=$(echo "result = (${gentime}/1000); scale=2; result / 1" | bc -l)
                    structures=$(grep "Number of builder sequences" $logfile | cut -d' ' -f5)
                    explored=$(grep "Number of sequences explored" $logfile | cut -d' ' -f5)
                  
                    echo $gentime >> $tmpfilebuilders
                    echo "$project,$casestudy,$technique,$budget,$gentime,$structures,$explored" >> $tmpfile

                done
            done
        done
    done
}

function process_results_builders() {

    resultsdir=../tmp/
    tmpfile="results_builders/results_builders.csv"    
    [[ -f $tmpfile ]] && rm $tmpfile
    mkdir -p results_builders
    echo "case study ; builders ; time ; nMethods" > $tmpfile
    
    cases=$(ls $resultsdir)
    [[ $cases == "" ]] && echo "No Cases found in $currdir" && exit -1;
    for casestudy in $cases
    do
            testline=""
            currdir=$resultsdir/$casestudy
            logFile="$currdir/log.txt"

            numCLass=$(cat $logFile| grep "Amount of class"|cut -d':' -f2)

            builders=$(cat $logFile|sed -n -e '/Start All Methods:/,/End All Methods/ p'| sed -e '1d;$d') 
            nMethods=$(cat $logFile|grep "SIZE :"|cut -d':' -f2)
            nMethodsAll=$(cat $logFile|grep "Number of methods is:"|cut -d':' -f2)
            time=$(cat $logFile|grep "TOTAL Time"|cut -d':' -f2)

            echo "$casestudy ; $builders ; $time ; $nMethods"  >> $tmpfile
    done    

}


function clean_results_folders() {
   rm -r ./results-begen/
}


