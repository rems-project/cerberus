#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <setjmp.h>
#include <signal.h>
#include <inttypes.h>
#include <assert.h>

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

void cn_register_test_case(const char* suite, const char* name, cn_test_case_fn* func) {
    if (num_test_cases == CN_TEST_MAX_TEST_CASES) {
        printf("Tried to register too many tests.");
        exit(1);
    }

    test_cases[num_test_cases++] = (struct cn_test_case){
         .suite = suite,
         .name = name,
         .func = func
    };
}

void print_test_info(const char* suite, const char* name, int tests, int discards) {
    if (tests == 0 && discards == 0) {
        printf("Testing %s::%s:", suite, name);
    }
    else if (discards == 0) {
        printf("Testing %s::%s: %d runs", suite, name, tests);
    }
    else {
        printf("Testing %s::%s: %d runs; %d discarded", suite, name, tests, discards);
    }

    fflush(stdout);
}

int cn_test_main(int argc, char* argv[]) {
    int begin_time = cn_gen_get_milliseconds();
    set_cn_logging_level(CN_LOGGING_NONE);

    cn_gen_srand(cn_gen_get_milliseconds());
    enum cn_test_gen_progress progress_level = CN_TEST_GEN_PROGRESS_ALL;
    uint64_t seed = cn_gen_rand();
    int interactive = 0;
    enum cn_logging_level logging_level = CN_LOGGING_ERROR;
    int timeout = 0;
    int input_timeout = 5000;
    int exit_fast = 0;
    for (int i = 0; i < argc; i++) {
        char* arg = argv[i];

        if (strcmp("-S", arg) == 0 || strcmp("--seed", arg) == 0) {
            seed = strtoull(argv[i + 1], NULL, 16);
            i++;
        }
        else if (strcmp("-I", arg) == 0 || strcmp("--interactive", arg) == 0) {
            interactive = 1;
        }
        else if (strcmp("--logging-level", arg) == 0) {
            logging_level = strtol(argv[i + 1], NULL, 10);
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
    }

    if (interactive) {
        printf("Running in interactive mode\n");
    }

    if (timeout != 0) {
        printf("Running until timeout of %d seconds\n", timeout);
    }

    printf("Using seed: %016" PRIx64 "\n", seed);
    cn_gen_srand(seed);
    cn_gen_rand(); // Junk to get something to make a checkpoint from

    cn_gen_rand_checkpoint checkpoints[CN_TEST_MAX_TEST_CASES];
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
            checkpoints[i] = cn_gen_rand_save();
            cn_gen_set_input_timeout(input_timeout);
            enum cn_test_result result = test_case->func(progress_level);
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
                cn_gen_rand_restore(checkpoints[i]);
                cn_gen_set_input_timeout(0);
                test_case->func(CN_TEST_GEN_PROGRESS_NONE);
                set_cn_logging_level(CN_LOGGING_NONE);
                printf("\n\n");
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

    if (interactive && failed != 0) {
        printf("\nWould you like to replay a failure? [y/n] ");
        char resp[10];
        scanf("%s", resp);

        while (strcasecmp("y", resp) != 0 && strcasecmp("n", resp) != 0) {
            printf("Invalid choice\n");
            printf("Would you like to replay a failure? [y/n] ");
            scanf("%s", resp);
        }

        if (strcasecmp("n", resp) == 0) { return 0; }

        printf("\nWhich case would you like to rerun?\n");

        int j = 1;
        int mapToCase[failed];
        for (int i = 0; i < num_test_cases; i++) {
            if (results[i] == CN_TEST_FAIL) {
                struct cn_test_case* test_case = &test_cases[i];
                mapToCase[j - 1] = i;
                printf("%d. %s::%s\n", j, test_case->suite, test_case->name);
                j += 1;
            }
        }

        printf("> ");

        int testcase = 0;
        scanf("%d", &testcase);

        while (!(0 < testcase && testcase <= failed)) {
            printf("Invalid choice\n");
            printf("> ");
            scanf("%d", &testcase);
        }

        printf("\n");

        cn_gen_rand_restore(checkpoints[mapToCase[testcase - 1]]);
        set_cn_logging_level(CN_LOGGING_INFO);
        reset_cn_failure_cb();
        // raise(SIGTRAP); // Trigger breakpoint
        test_cases[mapToCase[testcase - 1]].func(0);
    }

    return !(failed == 0 && errored == 0);
}
