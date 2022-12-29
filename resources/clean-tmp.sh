#!/bin/bash
pushd $BUILDERS_HOME
ant clean-tmp -Dclass=$1
popd