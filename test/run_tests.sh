#!/bin/bash

# Note: This script must be run from the root directory of the repository
#       since the process.* scripts using relative paths (for StarExec).

SCRIPT_DIR=$(dirname "$(readlink -f "$0")")
TESTS_SMT_COMP_DIR="${SCRIPT_DIR}/smt-comp"
TESTS_NON_SMT_COMP_DIR="${SCRIPT_DIR}/extensions/non-smtcomp"
TESTS_Z3_DIR="${SCRIPT_DIR}/extensions/z3"
TESTS_ASRT_COUNT_DIR="${SCRIPT_DIR}/asrt-count"

RED='\033[0;31m'
GREEN='\033[0;32m'
NOCOLOR='\033[0m'

exitcode=0

die()
{
  echo "$1"
  exit 1
}

runtest()
{
  echo "... with seed $3"
	for test in $1/*.smt2; do
		echo ${test}
		tname=`basename $test`
		tname=${tname%.*}
		result=$(diff <($2  ${test} $3) $1/expect/${tname}.$3.$4.expect)
		if [ ! -z "$result" ]
    then
			echo -e "${RED}error:${NOCOLOR} Difference between expected and actual result:"
			echo $result
			exitcode=1
		fi
	done
}

[ -d "${TESTS_SMT_COMP_DIR}" ] || die "directory '${TESTS_SMT_COMP_DIR}' does not exist"
[ -d "${TESTS_SMT_COMP_DIR}/expect" ] || die "directory '${TESTS_SMT_COMP_DIR}/expect' does not exist"

[ -d "${TESTS_NON_SMT_COMP_DIR}" ] || die "directory '${TESTS_NON_SMT_COMP_DIR}' does not exist"
[ -d "${TESTS_NON_SMT_COMP_DIR}/expect" ] || die "directory '${TESTS_NON_SMT_COMP_DIR}/expect' does not exist"

[ -d "${TESTS_Z3_DIR}" ] || die "directory '${TESTS_Z3_DIR}' does not exist"
[ -d "${TESTS_Z3_DIR}/expect" ] || die "directory '${TESTS_Z3_DIR}/expect' does not exist"

[ -d "${TESTS_ASRT_COUNT_DIR}" ] || die "directory '${TESTS_ASRT_COUNT_DIR}' does not exist"
[ -d "${TESTS_ASRT_COUNT_DIR}/expect" ] || die "directory '${TESTS_ASRT_COUNT_DIR}/expect' does not exist"


echo "Run single-query/industry challenge track scrambler..."
runtest "${TESTS_SMT_COMP_DIR}" "${SCRIPT_DIR}"/../process.single-query-challenge-track 0 single
runtest "${TESTS_SMT_COMP_DIR}" "${SCRIPT_DIR}"/../process.single-query-challenge-track 1234 single
echo -e "\nRun incremental track scrambler..."
runtest "${TESTS_SMT_COMP_DIR}" "${SCRIPT_DIR}"/../process.incremental-track 0 incremental
runtest "${TESTS_SMT_COMP_DIR}" "${SCRIPT_DIR}"/../process.incremental-track 1234 incremental
echo -e "\nRun unsat-core track scrambler..."
runtest "${TESTS_SMT_COMP_DIR}" "${SCRIPT_DIR}"/../process.unsat-core-track 0 unsat-core
runtest "${TESTS_SMT_COMP_DIR}" "${SCRIPT_DIR}"/../process.unsat-core-track 1234 unsat-core
echo -e "\nRun model-validation track scrambler..."
runtest "${TESTS_SMT_COMP_DIR}" "${SCRIPT_DIR}"/../process.model-val-track 0 model-val
runtest "${TESTS_SMT_COMP_DIR}" "${SCRIPT_DIR}"/../process.model-val-track 1234 model-val


echo -e "\nRun non-SMTCOMP scrambler..."
runtest ${TESTS_NON_SMT_COMP_DIR} ${SCRIPT_DIR}/../process.non-smtcomp 0 non-smtcomp
runtest ${TESTS_NON_SMT_COMP_DIR} ${SCRIPT_DIR}/../process.non-smtcomp 1234 non-smtcomp
echo -e "\nRun Z3 scrambler..."
runtest ${TESTS_Z3_DIR} ${SCRIPT_DIR}/../process.z3 0 z3
runtest ${TESTS_Z3_DIR} ${SCRIPT_DIR}/../process.z3 1234 z3

echo -e "\nRun assertion counter..."
runtest "${TESTS_ASRT_COUNT_DIR}" "${SCRIPT_DIR}"/../process.assertion-count 0 asrt-count

if [ $exitcode -ne 0 ]
then
	echo -e "${RED}errors occurred${NOCOLOR}"
else
	echo -e "${GREEN}success${NOCOLOR}"
fi

exit $exitcode
