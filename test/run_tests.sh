#!/bin/bash

SCRIPT_DIR=$(dirname "$(readlink -f "$0")")
TESTS="${SCRIPT_DIR}/*.smt2"
EXPECT_DIR=${SCRIPT_DIR}/expect
RED='\033[0;31m'
GREEN='\033[0;32m'
NOCOLOR='\033[0m'

exitcode=0

runtest()
{
	for test in $TESTS; do
		echo ${test}
		tname=`basename $test`
		tname=${tname%.*}
		result=$(diff <($1  ${test} $2) ${EXPECT_DIR}/${tname}.$2.$3.expect)
		if [ -z "$result" ]; then
			echo "SUCCESS"
		else
			echo -e "${RED}ERROR:${NOCOLOR} Difference between expected and actual result:"
			echo $result
			exitcode=1
		fi
	done
}

runtest ./process.single-query-challenge-track 0 single 
runtest ./process.single-query-challenge-track 1234 single
runtest ./process.incremental-track 0 incremental
runtest ./process.incremental-track 1234 incremental
runtest ./process.unsat-core-track 0 unsat-core
runtest ./process.unsat-core-track 1234 unsat-core

if [ $exitcode -ne 0 ]
then
	echo -e "${RED}Errors occurred${NOCOLOR}"
else
	echo -e "${GREEN}Success${NOCOLOR}"
fi

exit $exitcode
