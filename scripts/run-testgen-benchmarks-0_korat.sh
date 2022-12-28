#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

clean_results_folders


# Todo lo de Korat
cases="caso1 caso2 caso3"
techniques="beapi korat"
budgets="3 4 5 6 7 8"


for casestudy in $cases 
do
    for technique in $techniques 
    do
        for budget in $budgets
        do
            cmd="timeout $TO ./run-testgen.sh 0_korat $casestudy $technique $budget"
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


process_results_beapi_vs_korat;
    
