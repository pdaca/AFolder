# AFolder - Solver for Array Folds Logic.

## 0. License
Copyright (c) 2016 Przemyslaw Daca.
This software is distributed under the MIT Licences. This software is
based on TinyXML library (http://www.grinninglizard.com/tinyxml/)

## 1. Requirements
AFolder requires the Z3 theorem prover to be
installed (https://github.com/Z3Prover/z3).

## 2. Compilation
Type 'make' to compile.

## 3. Usage example
./afolder benchmarks/markdown2.smt benchmarks/markdown2.xml -model

The input is an SMT formula, and an XML formula that is a functional description of folds.

## 4. Running benchmarks
To run all benchmarks execute  './run_benchmarks.sh'
