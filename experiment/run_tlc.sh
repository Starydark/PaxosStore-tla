#!/bin/bash

declare -a configs

pwd

rm -rf out

mkdir -p out

for file in Eager_config/*.ini; do
    name=`echo $file | awk -F "/" '{print $2}' | awk -F "." '{print $1}'`
    python3 tlcwrapper.py $file "out/$name"
done

