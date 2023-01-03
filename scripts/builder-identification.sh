#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

projects="$1"
casestudy="$2"

TO=60m
function run_identification(){
    for project in $projects
    do
        for case in $casestudy 
        do
            echo "************"
            run_identify_builders $project $case
            echo "************"

        done
    done
}

function run_identify_builders(){
    project=$1
    casestudy=$2
    
    pushd $BE_EXP_SRC/$project
    ant
    #For Infer.
    # mkdir -p "$BE_EXP_SRC/src/" && cp -r $BE_EXP_SRC/$project/src/main/java/* $BE_EXP_SRC/src
    mkdir -p "$BE_EXP_SRC/src/" && cp -r src/main/java/* $BE_EXP_SRC/src
    mkdir -p "$BE_EXP_SRC/build/classes" && cp -r build/classes/* $BE_EXP_SRC/build/classes
  
    #Log for builders tools.
    rm -r $BE_EXP_SRC/tmp/$casestudy/*
    popd
    pushd $BE_EXP_SRC

    SECONDS=0
    cmd="java -cp $project/build/classes/:lib/korat.jar:lib/identificationBuilders.jar main.Builders $casestudy > tmp/$casestudy/console.dat"
    
    echo ">> Executing: $cmd"
    echo "$cmd" 
    bash -c "$cmd"

    #Must be copy to beapi directory. Escape '('.
    cp builders.txt tmp/$casestudy/

    #Rm temporary folders.
    rm builders.txt
    folder=${casestudy%%.*}
    rm -r $BE_EXP_SRC/$folder
    rm -r $BE_EXP_SRC/src/
    rm -r $BE_EXP_SRC/build/classes

    popd
}

run_identification;

echo "************"
echo "Report"
process_results_builders_display $project $casestudy;
echo "************"
