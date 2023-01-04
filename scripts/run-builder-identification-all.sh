#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

clean_results_folders

./run-builder-identification-0_korat.sh
./run-builder-identification-1_kiasan.sh
./run-builder-identification-2_roops.sh
./run-builder-identification-3_fajita.sh
./run-builder-identification-4_real_world.sh


process_results_builders;
    
