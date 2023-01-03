#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

clean_results_folders

./beapi-optimizations-0_korat.sh
./beapi-optimizations-1_kiasan.sh
./beapi-optimizations-2_roops.sh
./beapi-optimizations-3_fajita.sh
./beapi-optimizations-4_real_world.sh


process_results_beapi_vs_korat;
    
