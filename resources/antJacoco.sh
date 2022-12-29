#!/bin/bash
pushd $BUILDERS_HOME
ant coverage -Dclass=$1 -Dseed=$2 -DchromoNumber=$3 -DtestDirBuiCovPath=$4 -DpackDot=$5
ant clean-jacoco-test -Dclass=$1 -Dseed=$2 -DchromoNumber=$3 -DtestDirBuiCovPath=$4 -DpackDot=$5
popd $BUILDERS_HOME
