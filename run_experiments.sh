#!/bin/bash

TOOL='./afolder'

BENCHMARKS="experiments/sum_test.smt,experiments/sum_test.xml,
experiments/sum_test_mix.smt,experiments/sum_test_mix.xml,
experiments/sum_test_badguard.smt,experiments/sum_test_badguard.xml,
experiments/sum_test_badmix.smt,experiments/sum_test_badmix.xml,
"

for TEST in ${BENCHMARKS}
do
    IFS=","
    set ${TEST}
    CMD="${TOOL} $1 $2 $3 -model"
    echo "Running "${CMD}
    eval ${CMD}
    echo "-----------"
    echo
done
