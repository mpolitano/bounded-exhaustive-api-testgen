#!/bin/bash
source $scriptsdir/common.sh

TO=60m

function process_results_beapi_vs_korat() {
    techniques="korat beapi/matching/builders"

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

    resultsdir=./results-begen/
    tmpfile="$resultsdir/results_testgen_benchmarks.csv"

    if [[ $technique == "beapi"* ]]; then
        resultsdir=results-begen/$project/$casestudy/$technique/matching/builders/$budget/
    else
        resultsdir=results-begen/$project/$casestudy/$technique/$budget/
    fi

    if [[ ! -f $tmpfile ]] ; then
        echo "Project,Class,Technique,Budget,Time,Structures,Explored" > $tmpfile
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
    echo "$project,$casestudy,$technique,$budget,$gentime,$structures,$explored" >> $tmpfile

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

                if [[ $technique == "beapi/matching/discover" ]]; then
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

function process_results_optimizations_display() {
    project=$1
    casestudy=$2
    technique=$3
    budget=$4

    resultsdir=./results-optimizations/
    tmpfile="$resultsdir/results_optimizations.csv"

    tmpfilebuilders="builders.txt"
    # [[ -f $tmpfile ]] && rm $tmpfile
    [[ -f $tmpfilebuilders ]] && rm $tmpfilebuilders
    if [[ ! -e $tmpfile ]] ; then
        echo "Project,Class,Technique,Budget,Time,Structures,Explored" > $tmpfile
    fi
    echo "Project,Class,Technique,Budget,Time,Structures,Explored"
    projects=$(ls $resultsdir)
    [[ $projects == "" ]] && echo "No proyects found in $currdir" && exit -1;
  
    currdir=$resultsdir/$project/$casestudy/$technique/$budget/
    logfile=$currdir/log.txt

    gentime=""
    structures=""
    explored=""

    gentime=$(grep "Bounded exhaustive generation time" $logfile | cut -d' ' -f5)
    # gentime=$(echo "result = (${gentime}/1000); scale=2; result / 1" | bc -l)
    structures=$(grep "Number of builder sequences" $logfile | cut -d' ' -f5)
    explored=$(grep "Number of sequences explored" $logfile | cut -d' ' -f5)
  
    echo $gentime >> $tmpfilebuilders
    echo "$project,$casestudy,$technique,$budget,$gentime,$structures,$explored"
    echo "$project,$casestudy,$technique,$budget,$gentime,$structures,$explored" >> $tmpfile

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

            echo "$project $casestudy ; $builders ; $time ; $nMethods"  >> $tmpfile
    done    

}

function process_results_builders_display() {
    
    project=$1
    casestudy=$2
    resultsdir=../tmp/
    tmpfile="results_builders/results_builders.csv"    

    echo "case study ; builders ; time ; nMethods" 
    
    if [[ ! -f $tmpfile ]] ; then
        echo "case study ; builders ; time ; nMethods" > $tmpfile
    fi
    testline=""
    currdir=$resultsdir/$casestudy
    logFile="$currdir/log.txt"

    numCLass=$(cat $logFile| grep "Amount of class"|cut -d':' -f2)

    builders=$(cat $logFile|sed -n -e '/Start All Methods:/,/End All Methods/ p'| sed -e '1d;$d') 
    nMethods=$(cat $logFile|grep "SIZE :"|cut -d':' -f2)
    nMethodsAll=$(cat $logFile|grep "Number of methods is:"|cut -d':' -f2)
    time=$(cat $logFile|grep "TOTAL Time"|cut -d':' -f2)

    echo "$project $casestudy ; $builders ; $time ; $nMethods"
    echo "$project $casestudy ; $builders ; $time ; $nMethods" >> $tmpfile

}


function process-results-inclusion() {
    techniques=$1

    resultsdir=./results-begen-inclusion/
    tmpfile="$resultsdir/processresults.csv"
    # [[ -f $tmpfile ]] && rm $tmpfile
    echo "Project,Class,Technique,Budget,Other Bdgt,Structures,Other Strs,Not Included,Not Incl %" > $tmpfile
    echo "Project,Class,Technique,Budget,Other Bdgt,Structures,Other Strs,Not Included,Not Incl %"
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
                    for inclfile in $(ls $currdir/inclusion-res* | sort -V)
                    do
                        otherbudget=${inclfile##*-}
                        otherbudget=${otherbudget%.txt}

                        structures=$(grep "Structures:" $inclfile | cut -d" " -f2)
                        otherstrs=$(grep "Target structures" $inclfile | cut -d" " -f3)
                        notincluded=$(grep "Structures not in target" $inclfile | cut -d" " -f5)
                        notinclpct=$(echo "result = ($notincluded/$structures) * 100; scale=1 ; result/1 " | bc -l)

                        # repeatedstrs=$(grep "Structures repeated in target" $inclfile | cut -d" " -f5)
                        # [[ ! $repeatedstrs == "0" ]] && echo ">> WARNING: Repeated structures in target. See: $inclfile"

                        echo "$project,$casestudy,$technique,$budget,$otherbudget,$structures,$otherstrs,$notincluded,$notinclpct" >> $tmpfile
                        echo "$project,$casestudy,$technique,$budget,$otherbudget,$structures,$otherstrs,$notincluded,$notinclpct"

                    done
                done
            done
        done
    done
    # cat $tmpfile | sort -V

}
