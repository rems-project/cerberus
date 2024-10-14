#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <setjmp.h>
#include <signal.h>
#include <inttypes.h>

#include <cn-executable/utils.h>

#include <cn-testing/result.h>
#include <cn-testing/rand.h>

typedef enum cn_test_result cn_test_case_fn(void);

struct cn_test_case {
    char* suite;
    char* name;
    cn_test_case_fn* func;
};

#define CN_TEST_MAX_TEST_CASES 1000

static struct cn_test_case test_cases[CN_TEST_MAX_TEST_CASES];
static uint16_t num_test_cases = 0;

void cn_register_test_case(char* suite, char* name, cn_test_case_fn* func) {
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

int cn_test_main(int argc, char* argv[]) {
    set_cn_logging_level(CN_LOGGING_NONE);

    cn_gen_srand(time(NULL));
    uint64_t seed = cn_gen_rand();
    int interactive = 0;
    enum cn_logging_level logging_level = CN_LOGGING_ERROR;
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
    }

    if (interactive) {
        printf("Running in interactive mode\n");
    }

    printf("Using seed: %016" PRIx64 "\n", seed);
    cn_gen_srand(seed);
    cn_gen_rand(); // Junk to get something to make a checkpoint from

    int passed = 0;
    int failed = 0;
    int errored = 0;
    int skipped = 0;

    cn_gen_rand_checkpoint checkpoints[CN_TEST_MAX_TEST_CASES];
    enum cn_test_result results[CN_TEST_MAX_TEST_CASES];
    for (int i = 0; i < num_test_cases; i++) {
        struct cn_test_case* test_case = &test_cases[i];
        printf("Testing %s::%s: ", test_case->suite, test_case->name);
        checkpoints[i] = cn_gen_rand_save();
        results[i] = test_case->func();
        switch (results[i]) {
        case CN_TEST_PASS:
            passed++;
            printf("PASSED\n");
            break;
        case CN_TEST_FAIL:
            failed++;
            printf("FAILED\n");
            set_cn_logging_level(logging_level);
            cn_gen_rand_restore(checkpoints[i]);
            test_case->func();
            set_cn_logging_level(CN_LOGGING_NONE);
            break;
        case CN_TEST_GEN_FAIL:
            errored++;
            printf("FAILED TO GENERATE VALID INPUT\n");
            break;
        case CN_TEST_SKIP:
            skipped++;
            printf("SKIPPED\n");
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
        reset_cn_exit_cb();
        // raise(SIGTRAP); // Trigger breakpoint
        test_cases[mapToCase[testcase - 1]].func();
    }

    return !(failed == 0 && errored == 0);
}
