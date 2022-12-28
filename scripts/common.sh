#!/bin/bash

# IMPORTANT: Must set this variable
#export BE_EXP_SRC=


if [ -z $BE_EXP_MAXHEAP ]; then
    BE_EXP_MAXHEAP="8g"
fi

file_to_string() {
    strres=$(cat $1 | grep -v "#" | paste -s -d "$2" \-)
}

clean_and_compile() {
    cmd="ant clean clean-auto-tests compile > /dev/null"
    echo ""
    echo "> Cleaning up and compiling project: $cmd"
    bash -c "$cmd"
}

