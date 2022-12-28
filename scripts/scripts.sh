#!/bin/bash
source $scriptsdir/common.sh

TO=60m

function run_identify_builders(){
    project=$1
    casestudy=$2
    pushd $BE_EXP_SRC/$project
    ant
    mkdir -p "$BE_EXP_SRC/src/" && cp -r $BE_EXP_SRC/$project/src/main/java/* $BE_EXP_SRC/src/
    mkdir -p "$BE_EXP_SRC/build/classes" && cp -r $BE_EXP_SRC/$project/build/classes/* $BE_EXP_SRC/build/classes/
    rm -r $BE_EXP_SRC/tmp/$casestudy/*
    popd
    pushd $BE_EXP_SRC
    SECONDS=0
    echo "aca"
    echo $(pwd)
    cmd="java -cp lib/:lib/korat.jar:$project/build/classes/ main.Builders $casestudy"
    popd

    echo "$cmd" 
    bash -c "$cmd"
    cp builders.txt tmp/$casestudy/
    cp class-list.txt tmp/$casestudy/
}

function run_beapi_korat() {
    for project in $projects
    do
        for casestudy in $cases 
        do
            for technique in $techniques 
            do
                for budget in $budgets
                do
                    cmd="timeout $TO ./run-begen-experiment.sh $project $casestudy $technique $budget graph builders"
                    echo "************"
                    echo ">> Executing: $cmd"
                    bash -c "$cmd"
                    if [ $? -eq 124 ]; then 
                        echo ">> Execution timed out"
                        break;
                    fi
                done
            done
        done
    done
}

function process_results_beapi_vs_korat() {
    techniques="korat beapi/graph/builders"

    resultsdir=./results-begen/
    tmpfile="$resultsdir/results_beapi_vs_korat.csv"

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

function run_SM_BLD() {
    for project in $projects
    do
        for casestudy in $cases 
        do
            for technique in $techniques 
            do
                for budget in $budgets
                do
                    cmd="timeout $TO ./run-begen-experiment.sh $project $casestudy $technique $budget graph builders"
                    echo "************"
                    echo ">> Executing: $cmd"
                    bash -c "$cmd"
                    if [ $? -eq 124 ]; then 
                        echo ">> Execution timed out"
                        # break;
                        break 3;
                    fi
                done
            done
        done
    done
}

function run_SM() {
    for project in $projects
    do
        for casestudy in $cases 
        do
            for technique in $techniques 
            do
                for budget in $budgets
                do
                    cmd="timeout $TO ./run-begen-experiment.sh $project $casestudy $technique $budget graph no-builders"
                    echo "************"
                    echo ">> Executing: $cmd"
                    bash -c "$cmd"
                    if [ $? -eq 124 ]; then 
                        echo ">> Execution timed out"
                        # break;
                        break 3;

                    fi
                done
            done
        done
    done
}

function run_BLD() {
    for project in $projects
    do
        for casestudy in $cases 
        do
            for technique in $techniques 
            do
                for budget in $budgets
                do
                    cmd="timeout $TO ./run-begen-experiment.sh $project $casestudy $technique $budget no-matching builders"
                    echo "************"
                    echo ">> Executing: $cmd"
                    bash -c "$cmd"
                    if [ $? -eq 124 ]; then 
                        echo ">> Execution timed out"
                        # break;
                        break 3;
                    fi
                done
            done
        done
    done
}


function run_No_Opt() {
    for project in $projects
    do
        for casestudy in $cases 
        do
            for technique in $techniques 
            do
                for budget in $budgets
                do
                    cmd="timeout $TO ./run-begen-experiment.sh $project $casestudy $technique $budget no-matching no-builders"
                    echo "************"
                    echo ">> Executing: $cmd"
                    bash -c "$cmd"
                    if [ $? -eq 124 ]; then 
                        echo ">> Execution timed out"
                        # break;
                        break 3;
                    fi
                done
            done
        done
    done
}

function process_results_optimizations() {
    resultsdir=./results-begen/
    techniques="beapi/graph/builders beapi/graph/no-builders beapi/no-matching/builders beapi/no-matching/no-builders"

    tmpfile="$resultsdir/results_optimizations.csv"
    tmpfilebuilders="builders.txt"
    [[ -f $tmpfile ]] && rm $tmpfile
    [[ -f $tmpfilebuilders ]] && rm $tmpfilebuilders
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

                if [[ $technique == "beapi/graph/discover" ]]; then
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

                    if [[ $technique == "korat" ]]; then
                        gentime=$(grep "Overall time" $logfile | cut -d' ' -f3)
                        structures=$(grep "New found" $logfile | cut -d':' -f2)
                        explored=$(grep "Total explored" $logfile | cut -d':' -f2)
                    else
                        gentime=$(grep "Bounded exhaustive generation time" $logfile | cut -d' ' -f5)
                        # gentime=$(echo "result = (${gentime}/1000); scale=2; result / 1" | bc -l)
                        structures=$(grep "Number of builder sequences" $logfile | cut -d' ' -f5)
                        explored=$(grep "Number of sequences explored" $logfile | cut -d' ' -f5)
                    fi
                    echo $gentime >> $tmpfilebuilders
                    echo "$project,$casestudy,$technique,$budget,$gentime,$structures,$explored" >> $tmpfile

                done
            done
        done
    done
}

function clean_results_folders() {
   rm -r ./results-begen/
}


