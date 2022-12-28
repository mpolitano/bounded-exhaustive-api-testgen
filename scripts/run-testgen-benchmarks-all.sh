#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

clean_results_folders



./run-testgen-0_korat.sh
./run-testgen-1_kiasan.sh
...



process_results_beapi_vs_korat;
    
