#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

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
    mkdir -p "$BE_EXP_SRC/src/" && cp -r src/main/java/* $BE_EXP_SRC/src
    mkdir -p "$BE_EXP_SRC/build/classes" && cp -r build/classes/* $BE_EXP_SRC/build/classes
    #Log for builders tools.
    popd

    pushd $BE_EXP_SRC
    #Set scope 5
    cp $scriptsdir/literals/literals5.txt resources/literals.txt
    cp $scriptsdir/properties/scope5.all.canonicalizer.properties resources/scope.canonicalizer.properties

    rm -r tmp/$casestudy/*
    mkdir -p tmp/$casestudy/
    log=tmp/$casestudy/console.log
    log=$BE_EXP_SRC/tmp/$casestudy/console.log
    if [ -h log ] && [ ! -f log ]; then
        rm log
    fi
    SECONDS=0
    cmd="java -cp $project/build/classes/:lib/korat.jar:lib/identificationBuilders.jar main.Builders $casestudy > $log"
    
    echo ">> Executing: $cmd"
    echo "$cmd" 
    bash -c "$cmd"


    cat builders.txt|sed -r 's/[)]+/\\)/g'|sed -r 's/[(]+/\\(/g' > tmpBuilders.txt 

    mv tmpBuilders.txt builders.txt
    #Must be copy to beapi directory. Escape '('.
    mkdir -p $scriptsdir/results-builders/$project/$casestudy/
    cp builders.txt $scriptsdir/results-builders/$project/$casestudy/

    # Rm temporary folders.
    # rm tmpBuilders.txt
    rm builders.txt
    folder=${casestudy%%.*}
    rm -r $BE_EXP_SRC/$folder
    rm -r $BE_EXP_SRC/src/
    # rm -r $BE_EXP_SRC/inferFiles
    rm -r $BE_EXP_SRC/build/



    popd
}

run_identification;

echo "************"
echo "Report"
process_results_builders_display $project $casestudy;
echo "************"
