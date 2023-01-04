#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh

clean_results_folders

./run-testgen-beapi-optimizations-0_korat.sh
./run-testgen-beapi-optimizations-1_kiasan.sh
./run-testgen-beapi-optimizations-2_roops.sh
./run-testgen-beapi-optimizations-3_fajita.sh
./run-testgen-beapi-optimizations-4_real_world.sh



# process_results_beapi_vs_korat;
    
