#!/bin/bash 

source $BE_EXP_SRC/scripts/common.sh

resultsdir=./results-begen-serialize/
tmpfile="processresults.csv.tmp"
[[ -f $tmpfile ]] && rm $tmpfile

function process_results() {
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

                        repeatedstrs=$(grep "Structures repeated in target" $inclfile | cut -d" " -f5)
                        [[ ! $repeatedstrs == "0" ]] && echo ">> WARNING: Repeated structures in target. See: $inclfile"

                        echo "$project,$casestudy,$technique,$budget,$otherbudget,$structures,$otherstrs,$notincluded,$notinclpct" >> $tmpfile

                    done
                done
            done
        done
    done
}


echo "Project,Class,Technique,Budget,Other Bdgt,Structures,Other Strs,Not Included,Not Incl %"

techniques="korat beapi/graph/builders"
process_results

cat $tmpfile | sort -V
rm $tmpfile

