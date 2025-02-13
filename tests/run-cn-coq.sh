#!/usr/bin/env bash

# CI test for CN Coq extraction.
# OPAM package `cn-coq` must be installed.

set -uo pipefail

# Parse command line options
STOP_ON_ERROR=0
SINGLE_FILE=""
USE_DUNE=0
while getopts "def:" opt; do
    case ${opt} in
        d)
            USE_DUNE=1
            ;;
        e)
            STOP_ON_ERROR=1
            ;;
        f)
            SINGLE_FILE="${OPTARG}"
            STOP_ON_ERROR=1  # -f implies -e
            ;;
        *)
            echo "Usage: $0 [-e] [-f file]"
            echo "  -e  Stop on error and preserve temporary directory"
            echo "  -f  Run single test file (implies -e)"
            echo "  -d  Use dune to run CN"
            exit 1
            ;;
    esac
done

DIRNAME=$(dirname "$0")

# If single file specified, use that, otherwise find all .c files
if [ -n "${SINGLE_FILE}" ]; then
    if [ ! -f "${DIRNAME}/cn/${SINGLE_FILE}" ]; then
        echo "Error: Test file ${DIRNAME}/cn/${SINGLE_FILE} not found"
        exit 1
    fi
    SUCC="${DIRNAME}/cn/${SINGLE_FILE}"
else
    SUCC=$(find "${DIRNAME}"/cn -name '*.c' | grep -v '\.error\.c')
fi

FAILED=""
TOTAL=$(echo "${SUCC}" | grep -c '^')
CURRENT=1
PASSED_COUNT=0
FAILED_COUNT=0

if [ ${USE_DUNE} -eq 1 ]; then
    CERB_RUNTIME="$(realpath "../runtime/")"
    CN=(env CERB_RUNTIME="${CERB_RUNTIME}" ${WITH_CN:=dune exec cn --})
    COQ_CN_THEORIES_DIR="$(realpath "../_build/default/backend/cn/coq")"
    COQ_MAKEFILE_FLAGS="-R . Top -R ${COQ_CN_THEORIES_DIR}/Cerberus/ Cerberus -R ${COQ_CN_THEORIES_DIR}/Cn/ Cn"
else
    CN=(cn)
    COQ_MAKEFILE_FLAGS=
fi

for TEST in ${SUCC}; do
    # Create temporary directory for this test run
    TMPDIR=$(mktemp -d /tmp/cn-verify.XXXXXX)
    # Create Coq export filename in TMPDIR by replacing .c with .v and taking basename
    COQ_EXPORT="${TMPDIR}/$(basename "${TEST%.c}.v")"
    printf "[%d/%d] %s:\n" "${CURRENT}" "${TOTAL}" "${TEST}"
    
    if timeout 60 "${CN[@]}" verify "${TEST}" --coq-export-file="${COQ_EXPORT}" > "${TMPDIR}/cn.log" 2>&1; then
        printf "  CN verify:    \033[32mSUCCESS\033[0m\n"
        
        # Copy Coq file to temp dir and try to compile it
        if (cd "${TMPDIR}" && coq_makefile ${COQ_MAKEFILE_FLAGS} -o Makefile "$(basename "${COQ_EXPORT}")" && make) > "${TMPDIR}/coq.log" 2>&1; then
            printf "  Coq compile:  \033[32mSUCCESS\033[0m\n"
            rm -rf "${TMPDIR}"
            PASSED_COUNT=$((PASSED_COUNT + 1))
        else
            printf "  Coq compile:  \033[31mFAIL\033[0m\n"
            printf "\nOutput from failed Coq compilation:\n"
            cat "${TMPDIR}/coq.log"
            printf "\n"
            if [ ${STOP_ON_ERROR} -eq 1 ]; then
                printf "Temporary directory preserved at: ${TMPDIR}\n"
                exit 1
            fi
            rm -rf "${TMPDIR}"
            FAILED+=" ${TEST}"
            FAILED_COUNT=$((FAILED_COUNT + 1))
        fi
    else
        printf "  CN verify:    \033[31mFAIL\033[0m\n"
        printf "\nOutput from failed test:\n"
        cat "${TMPDIR}/cn.log"
        printf "\n"
        if [ ${STOP_ON_ERROR} -eq 1 ]; then
            printf "Temporary directory preserved at: ${TMPDIR}\n"
            exit 1
        fi
        rm -rf "${TMPDIR}"
        FAILED+=" ${TEST}"
        FAILED_COUNT=$((FAILED_COUNT + 1))
    fi
    CURRENT=$((CURRENT + 1))
done

if [ -z "${FAILED}" ]; then
    printf "\nAll %d tests passed!\n" "${TOTAL}"
    exit 0
else
    printf "\nOut of %d tests %d passed, %d tests failed\n" "${TOTAL}" "${PASSED_COUNT}" "${FAILED_COUNT}"
    exit 1
fi 