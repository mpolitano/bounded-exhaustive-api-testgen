#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

#Korat
projects="$1"
cases="$2"

TO=60m
function run_identification(){
    for project in $projects
    do
        for casestudy in $cases 
        do
            echo "************"
            run_identify_builders $project $casestudy
            echo "************"

        done
    done
}

function run_identify_builders(){
    project=$1
    casestudy=$2
    
    pushd $BE_EXP_SRC/$project
    ant
    popd
    mkdir -p "$BE_EXP_SRC/src/" && cp -r $BE_EXP_SRC/$project/src/main/java/* $BE_EXP_SRC/src
    mkdir -p "$BE_EXP_SRC/build/classes" && cp -r $BE_EXP_SRC/$project/build/classes/* $BE_EXP_SRC/build/classes
    rm -r $BE_EXP_SRC/tmp/$casestudy/*
    
    pushd $BE_EXP_SRC

    SECONDS=0

    cmd="java -cp $project/build/classes/:lib/korat.jar:lib/identificationBuilders.jar main.Builders $casestudy"
    
    echo ">> Executing: $cmd"
    echo "$cmd" 
    bash -c "$cmd"
    cp builders.txt tmp/$casestudy/

    #debo borrar las folders. TODO
    #rm -r $BE_EXP_SRC/

    rm -r $BE_EXP_SRC/src/
    rm -r $BE_EXP_SRC/build/classes
    popd
}
run_identification;
# process_results_builders;

