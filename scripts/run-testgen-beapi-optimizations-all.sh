#!/bin/bash

projectsdir=$BE_EXP_SRC
scriptsdir=$projectsdir/scripts
source $scriptsdir/scripts.sh
budgetMax="$1"


./run-testgen-beapi-optimizations-0_korat.sh $budgetMax
./run-testgen-beapi-optimizations-1_kiasan.sh $budgetMax
./run-testgen-beapi-optimizations-2_roops.sh $budgetMax
./run-testgen-beapi-optimizations-3_fajita.sh $budgetMax
./run-testgen-beapi-optimizations-4_real_world.sh $budgetMax

