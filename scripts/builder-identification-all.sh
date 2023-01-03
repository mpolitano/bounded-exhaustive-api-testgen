#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/process-results.sh

clean_results_folders

./builder-identification-0_korat.sh
./builder-identification-1_kiasan.sh
./builder-identification-2_roops.sh
./builder-identification-3_fajita.sh
./builder-identification-4_real_world.sh


process_results_builders;
    
