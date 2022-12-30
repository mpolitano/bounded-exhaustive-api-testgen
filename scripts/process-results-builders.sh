#!/bin/bash 


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

                # done
    

}

process_results