#!/bin/bash

TOOL='./afolder'

BENCHMARKS="benchmarks/markdown1.smt,benchmarks/markdown1.xml,
benchmarks/markdown2.smt,benchmarks/markdown2.xml,
benchmarks/markdown3.smt,benchmarks/markdown3.xml,
benchmarks/numa-864-10.smt,benchmarks/numa-864.xml,
benchmarks/numa-864-20.smt,benchmarks/numa-864.xml,
benchmarks/numa-864-40.smt,benchmarks/numa-864.xml,
benchmarks/standard_minInArray_false-unreach-call_ground.smt,benchmarks/standard_minInArray_false-unreach-call_ground.xml,
benchmarks/linear_sea.ch_true-unreach-call.smt,benchmarks/linear_sea.ch_true-unreach-call.xml
benchmarks/array_true-unreach-call3.smt,benchmarks/array_true-unreach-call3.xml,
benchmarks/standard_sentinel_true-unreach-call.smt,benchmarks/standard_sentinel_true-unreach-call.xml,
benchmarks/standard_find_true-unreach-call_ground.smt,benchmarks/standard_find_true-unreach-call_ground.xml,
benchmarks/standard_vararg_true-unreach-call_ground.smt,benchmarks/standard_vararg_true-unreach-call_ground.xml,
benchmarks/histogram-range8.smt,benchmarks/histogram-range.xml,-nosfsat
benchmarks/histogram-range9.smt,benchmarks/histogram-range.xml,-nosfsat
benchmarks/histogram-range10.smt,benchmarks/histogram-range.xml,-nosfsat
benchmarks/histogram-range11.smt,benchmarks/histogram-range.xml,-nosfsat
benchmarks/histogram-range11-unsat.smt,benchmarks/histogram-range.xml,-nosfsat
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
