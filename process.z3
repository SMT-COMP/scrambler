#!/bin/sh

# This is a wrapper script that allows the scrambler to be used as a
# preprocessor on StarExec.

# $1: benchmark filename
# $2: seed

ulimit -s 1048576
./scrambler -support-z3 true -seed "$2" < "$1"
