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
  echo "... with seed $2"
	for test in $TESTS; do
		echo ${test}
		tname=`basename $test`
		tname=${tname%.*}
		result=$(diff <($1  ${test} $2) ${EXPECT_DIR}/${tname}.$2.$3.expect)
		if [ ! -z "$result" ]
    then
			echo -e "${RED}error:${NOCOLOR} Difference between expected and actual result:"
			echo $result
			exitcode=1
		fi
	done
}

echo "Run single-query/industry challenge track scrambler..."
runtest ./process.single-query-challenge-track 0 single
runtest ./process.single-query-challenge-track 1234 single
echo -e "\nRun incremental track scrambler..."
runtest ./process.incremental-track 0 incremental
runtest ./process.incremental-track 1234 incremental
echo -e "\nRun unsat-core track scrambler..."
runtest ./process.unsat-core-track 0 unsat-core
runtest ./process.unsat-core-track 1234 unsat-core
echo -e "\nRun model-validation track scrambler..."
runtest ./process.model-val-track 0 model-val
runtest ./process.model-val-track 1234 model-val

if [ $exitcode -ne 0 ]
then
	echo -e "${RED}errors occurred${NOCOLOR}"
else
	echo -e "${GREEN}success${NOCOLOR}"
fi

exit $exitcode
