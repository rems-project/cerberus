#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <setjmp.h>
#include <signal.h>
#include <inttypes.h>
#include <assert.h>
#include <stdbool.h>

#include <cn-executable/utils.h>

#include <cn-testing/test.h>
#include <cn-testing/result.h>
#include <cn-testing/rand.h>
#include <cn-testing/alloc.h>
#include <cn-testing/size.h>

struct cn_test_case {
    const char* suite;
    const char* name;
    cn_test_case_fn* func;
};

#define CN_TEST_MAX_TEST_CASES 1000

static struct cn_test_case test_cases[CN_TEST_MAX_TEST_CASES];
static uint16_t num_test_cases = 0;

/**
 * Registers a test.
 *
 * @param suite The name of the test suite.
 * @param name The name of the test.
 * @param func The function pointer to the test.
 */
void cn_register_test_case(const char* suite, const char* name, cn_test_case_fn* func) {
    if (num_test_cases == CN_TEST_MAX_TEST_CASES) {
        fprintf(stderr, "Error: Tried to register too many tests.\n");
        exit(1);
    }

    test_cases[num_test_cases++] = (struct cn_test_case){
         .suite = suite,
         .name = name,
         .func = func
    };
}

/**
 * Prints information about a test.
 *
 * @param suite The name of the test suite.
 * @param name The name of the test.
 * @param tests The number of test runs.
 * @param discards The number of discarded test cases.
 */
void print_test_info(const char* suite, const char* name, int tests, int discards) {
    if (tests == 0 && discards == 0) {
        printf("Testing %s::%s:", suite, name);
    }
    else if (discards == 0) {
        printf("Testing %s::%s: %d runs", suite, name, tests);
    }
    else {
        printf("Testing %s::%s: %d runs, %d discards", suite, name, tests, discards);
    }

    fflush(stdout);
}

#if defined(__has_builtin) && !defined(__ibmxl__) && __has_builtin(__builtin_debugtrap)
#  define _cn_trap() __builtin_debugtrap()
#elif defined(__has_builtin) && !defined(__ibmxl__) && __has_builtin(__debugbreak)
#  define _cn_trap() __debugbreak()
#elif defined(_MSC_VER) || defined(__INTEL_COMPILER)
#  define _cn_trap() __debugbreak()
#elif defined(__ARMCC_VERSION)
#  define _cn_trap() __breakpoint(42)
#elif defined(__ibmxl__) || defined(__xlC__)
#  include <builtins.h>
#  define _cn_trap() __trap(42)
#elif defined(__DMC__) && defined(_M_IX86)
static inline void _cn_trap(void) { __asm int 3h; }
#elif defined(__i386__) || defined(__x86_64__)
static inline void _cn_trap(void) { __asm__ __volatile__("int3"); }
#elif defined(__thumb__)
static inline void _cn_trap(void) { __asm__ __volatile__(".inst 0xde01"); }
#elif defined(__aarch64__)
static inline void _cn_trap(void) { __asm__ __volatile__(".inst 0xd4200000"); }
#elif defined(__arm__)
static inline void _cn_trap(void) { __asm__ __volatile__(".inst 0xe7f001f0"); }
#elif defined (__alpha__) && !defined(__osf__)
static inline void _cn_trap(void) { __asm__ __volatile__("bpt"); }
#elif defined(_54_)
static inline void _cn_trap(void) { __asm__ __volatile__("ESTOP"); }
#elif defined(_55_)
static inline void _cn_trap(void) { __asm__ __volatile__(";\n .if (.MNEMONIC)\n ESTOP_1\n .else\n ESTOP_1()\n .endif\n NOP"); }
#elif defined(_64P_)
static inline void _cn_trap(void) { __asm__ __volatile__("SWBP 0"); }
#elif defined(_6x_)
static inline void _cn_trap(void) { __asm__ __volatile__("NOP\n .word 0x10000000"); }
#elif defined(__STDC_HOSTED__) && (__STDC_HOSTED__ == 0) && defined(__GNUC__)
#    define _cn_trap() __builtin_trap()
#else
#  include <signal.h>
#  if defined(SIGTRAP)
#    define _cn_trap() raise(SIGTRAP)
#  else
#    define _cn_trap() raise(SIGABRT)
#  endif
#endif

void cn_trap(void) { _cn_trap(); }

size_t cn_gen_compute_size(enum cn_gen_size_strategy strategy, int max_tests, size_t max_size, int max_discard_ratio, int successes, int recent_discards) {
    switch (strategy) {
    case CN_GEN_SIZE_QUARTILE:
        if (successes < max_tests / 4) {
            max_size /= 4;
        }
        else if (successes < max_tests / 2) {
            max_size /= 2;
        }
        else if (successes < 3 * (max_tests / 4)) {
            max_size /= 4;
            max_size *= 3;
        }

    case CN_GEN_SIZE_UNIFORM:
        ;
        size_t sz = cn_gen_uniform_cn_bits_u16(max_size + 1)->val + 1;
        return sz;

    case CN_GEN_SIZE_QUICKCHECK:
        ;
        size_t discard_divisor;
        if (max_discard_ratio > 0) {
            discard_divisor = (successes * max_discard_ratio / 3);
            if (discard_divisor < 1) {
                discard_divisor = 1;
            }
            else if (discard_divisor > 10) {
                discard_divisor = 10;
            }
        }
        else {
            discard_divisor = 1;
        }

        size_t potential_size;
        if ((successes / max_size) * max_size + max_size <= max_tests
            || successes >= max_tests
            || max_tests % max_size == 0) {
            potential_size = (successes % max_tests + recent_discards / discard_divisor);
        }
        else {
            potential_size = (successes % max_size) * max_size
                / (successes % max_size) + recent_discards / discard_divisor;
        }

        if (potential_size < max_size) {
            return potential_size + 1;
        }

        return max_size + 1;
    }
}

struct cn_test_reproduction {
    size_t size;
    cn_gen_rand_checkpoint checkpoint;
};

void cn_test_reproduce(struct cn_test_reproduction* repro) {
    cn_gen_set_size(repro->size);
    cn_gen_rand_restore(repro->checkpoint);
}

int cn_test_main(int argc, char* argv[]) {
    int begin_time = cn_gen_get_milliseconds();
    set_cn_logging_level(CN_LOGGING_NONE);

    cn_gen_srand(cn_gen_get_milliseconds());
    enum cn_test_gen_progress progress_level = CN_TEST_GEN_PROGRESS_ALL;
    uint64_t seed = cn_gen_rand();
    enum cn_logging_level logging_level = CN_LOGGING_ERROR;
    int timeout = 0;
    int input_timeout = 5000;
    int exit_fast = 0;
    int trap = 0;
    enum cn_gen_size_strategy sizing_strategy = 0;
    for (int i = 0; i < argc; i++) {
        char* arg = argv[i];

        if (strcmp("-S", arg) == 0 || strcmp("--seed", arg) == 0) {
            seed = strtoull(argv[i + 1], NULL, 16);
            i++;
        }
        else if (strcmp("--logging-level", arg) == 0) {
            logging_level = strtol(argv[i + 1], NULL, 10);
            i++;
        }
        else if (strcmp("--trace-granularity", arg) == 0) {
            set_cn_trace_granularity(strtol(argv[i + 1], NULL, 10));
            i++;
        }
        else if (strcmp("--progress-level", arg) == 0) {
            progress_level = strtol(argv[i + 1], NULL, 10);
            i++;
        }
        else if (strcmp("--input-timeout", arg) == 0) {
            input_timeout = strtol(argv[i + 1], NULL, 10);
            i++;
        }
        else if (strcmp("--null-in-every", arg) == 0) {
            set_null_in_every(strtol(argv[i + 1], NULL, 10));
            i++;
        }
        else if (strcmp("--until-timeout", arg) == 0) {
            timeout = strtol(argv[i + 1], NULL, 10);
            i++;
        }
        else if (strcmp("--exit-fast", arg) == 0) {
            exit_fast = 1;
        }
        else if (strcmp("--max-stack-depth", arg) == 0) {
            cn_gen_set_max_depth(strtoul(argv[i + 1], NULL, 10));
            i++;
        }
        else if (strcmp("--max-generator-size", arg) == 0) {
            uint64_t sz = strtoul(argv[i + 1], NULL, 10);
            assert(sz != 0);
            cn_gen_set_max_size(sz);
            i++;
        }
        else if (strcmp("--sized-null", arg) == 0) {
            set_sized_null();
        }
        else if (strcmp("--allowed-depth-failures", arg) == 0) {
            cn_gen_set_depth_failures_allowed(strtoul(argv[i + 1], NULL, 10));
            i++;
        }
        else if (strcmp("--allowed-size-split-backtracks", arg) == 0) {
            cn_gen_set_size_split_backtracks_allowed(strtoul(argv[i + 1], NULL, 10));
            i++;
        }
        else if (strcmp("--trap", arg) == 0) {
            trap = 1;
        }
        else if (strcmp("--sizing-strategy", arg) == 0) {
            sizing_strategy = strtoul(argv[i + 1], NULL, 10);
            i++;
        }
    }

    if (timeout != 0) {
        printf("Running until timeout of %d seconds\n", timeout);
    }

    printf("Using seed: %016" PRIx64 "\n", seed);
    cn_gen_srand(seed);
    cn_gen_rand(); // Junk to get something to make a checkpoint from

    struct cn_test_reproduction repros[CN_TEST_MAX_TEST_CASES];
    enum cn_test_result results[CN_TEST_MAX_TEST_CASES];
    memset(results, CN_TEST_SKIP, CN_TEST_MAX_TEST_CASES * sizeof(enum cn_test_result));

    int timediff = 0;

    do {
        for (int i = 0; i < num_test_cases; i++) {
            if (results[i] == CN_TEST_FAIL) {
                continue;
            }

            struct cn_test_case* test_case = &test_cases[i];
            if (progress_level == CN_TEST_GEN_PROGRESS_ALL) {
                print_test_info(test_case->suite, test_case->name, 0, 0);
            }
            repros[i].size = cn_gen_get_size();
            repros[i].checkpoint = cn_gen_rand_save();
            cn_gen_set_input_timeout(input_timeout);
            enum cn_test_result result = test_case->func(false, progress_level, sizing_strategy, 0);
            if (!(results[i] == CN_TEST_PASS && result == CN_TEST_GEN_FAIL)) {
                results[i] = result;
            }
            if (progress_level == CN_TEST_GEN_PROGRESS_NONE) {
                continue;
            }

            printf("\n");
            switch (result) {
            case CN_TEST_PASS:
                printf("PASSED\n");
                break;
            case CN_TEST_FAIL:
                printf("FAILED\n");

                set_cn_logging_level(logging_level);
                cn_printf(CN_LOGGING_ERROR, "\n");

                cn_test_reproduce(&repros[i]);
                test_case->func(true, CN_TEST_GEN_PROGRESS_NONE, sizing_strategy, trap);

                set_cn_logging_level(CN_LOGGING_NONE);
                printf("\n");

                break;
            case CN_TEST_GEN_FAIL:
                printf("FAILED TO GENERATE VALID INPUT\n");
                break;
            case CN_TEST_SKIP:
                printf("SKIPPED\n");
                break;
            }

            if (exit_fast && result == CN_TEST_FAIL) {
                goto outside_loop;
            }

            if (timeout != 0) {
                timediff = cn_gen_get_milliseconds() / 1000 - begin_time;
            }
        }
        if (timediff < timeout) {
            printf("\n%d seconds remaining, rerunning tests\n\n", timeout - timediff);
        }
    } while (timediff < timeout);

outside_loop:
    ;
    int passed = 0;
    int failed = 0;
    int errored = 0;
    int skipped = 0;

    for (int i = 0; i < num_test_cases; i++) {
        switch (results[i]) {
        case CN_TEST_PASS:
            passed++;
            break;
        case CN_TEST_FAIL:
            failed++;
            break;
        case CN_TEST_GEN_FAIL:
            errored++;
            break;
        case CN_TEST_SKIP:
            skipped++;
            break;
        }
    }

    printf("\nTesting Summary:\n");
    printf(
        "cases: %d, passed: %d, failed: %d, errored: %d, skipped: %d\n",
        num_test_cases, passed, failed, errored, skipped);

    return !(failed == 0 && errored == 0);
}
