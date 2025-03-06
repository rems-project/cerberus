#!/usr/bin/env bash

# CI test for CN Coq extraction.
# OPAM package `cn-coq` must be installed.

set -uo pipefail


# List of blacklisted files that are known to run out of memory in Coq.
# Paths must be relative to the 'tests/cn' directory.
# NB: tree16/as_partial_map/tree16.c is known to pass but takes a long time
BLACKLISTED_FILES=(
    tree16/as_partial_map/tree16.c
    tree16/as_mutual_dt/tree16.c
    mergesort.c
    mergesort_alt.c
    mutual_rec/mutual_rec2.c
)

# Parse command line options
VERBOSE_USAGE=0
STOP_ON_ERROR=0
SINGLE_FILE=""
USE_DUNE=0
COQ_PROOF_LOG=0
COQ_CHECK_PROOF_LOG=0

while getopts "dpef: v" opt; do
    case ${opt} in
        d)
            USE_DUNE=1
            ;;
        p)
            COQ_PROOF_LOG=1
            ;;
        c)
            COQ_CHECK_PROOF_LOG=1
            ;;
        e)
            STOP_ON_ERROR=1
            ;;
        f)
            SINGLE_FILE="${OPTARG}"
            STOP_ON_ERROR=1  # -f implies -e
            ;;
        v)
            VERBOSE_USAGE=1
            ;;
        *)
            echo "Usage: $0 [-e] [-f file] [-v]"
            echo "  -e  Stop on error and preserve temporary directory"
            echo "  -f  Run single test file (implies -e)"
            echo "  -d  Use dune to run CN"
            echo "  -p  Include proof log in Coq export"
            echo "  -c  Check proof log in Coq export"
            echo "  -v  Verbose output for resource usage logging"
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

# Filter out blacklisted files
for blacklisted in "${BLACKLISTED_FILES[@]}"; do
    SUCC=$(echo "${SUCC}" | grep -v "/${blacklisted}$")
done

FAILED=""
TOTAL=$(echo "${SUCC}" | grep -c '^')
CURRENT=1
PASSED_COUNT=0
FAILED_COUNT=0

if [ ${USE_DUNE} -eq 1 ]; then
    CN=(${WITH_CN:=dune exec cn --})
    unset CERB_INSTALL_PREFIX
    COQ_CN_THEORIES_DIR="$(realpath "../_build/default/backend/cn/coq")"
    COQ_MAKEFILE_FLAGS="-R . Top -R ${COQ_CN_THEORIES_DIR}/Cerberus/ Cerberus -R ${COQ_CN_THEORIES_DIR}/Cn/ Cn -R ${COQ_CN_THEORIES_DIR}/Reasoning/ Reasoning"
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
    
    # Build the verify command with optional proof log flag
    VERIFY_CMD=("${CN[@]}" verify "${TEST}" --coq-export-file="${COQ_EXPORT}")
    if [ ${COQ_PROOF_LOG} -eq 1 ]; then
        VERIFY_CMD+=("--coq-proof-log")
        if [ ${COQ_CHECK_PROOF_LOG} -eq 1 ]; then
            VERIFY_CMD+=("--coq-check-proof-log")
        fi
    fi
    
    VERIFY_START=$(date +%s)
    if timeout 60 "${VERIFY_CMD[@]}" > "${TMPDIR}/cn.log" 2>&1; then
        VERIFY_ELAPSED=$(($(date +%s) - ${VERIFY_START}))
        printf "  CN verify:    \033[32mSUCCESS\033[0m\n"
        
        if [ ${VERBOSE_USAGE} -eq 1 ]; then
            printf "      Verification time: %s sec.\n" "${VERIFY_ELAPSED}"
            if [ -f "${COQ_EXPORT}" ]; then
                FILESIZE=$(ls -lh "${COQ_EXPORT}" | awk '{print $5}')
                printf "      Generated .v file size: %s\n" "${FILESIZE}"
            else
                printf "      Generated .v file not found.\n"
            fi
        fi
        
        # Copy Coq file to temp dir and try to compile it
        COMPILE_START=$(date +%s)
        if (cd "${TMPDIR}" && coq_makefile ${COQ_MAKEFILE_FLAGS} -o Makefile "$(basename "${COQ_EXPORT}")" && { 
                if [ "${VERBOSE_USAGE}" -eq 1 ]; then 
                    /usr/bin/time -v make; 
                else 
                    make; 
                fi; 
             }) > "${TMPDIR}/coq.log" 2>&1; then
            COMPILE_ELAPSED=$(($(date +%s) - ${COMPILE_START}))
            if [ ${VERBOSE_USAGE} -eq 1 ]; then
                printf "      Coq compilation time: %s sec.\n" "${COMPILE_ELAPSED}"
            fi
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