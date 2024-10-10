#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <setjmp.h>
#include <signal.h>

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
    cn_gen_srand(time(NULL));
    uint64_t seed = cn_gen_rand();
    for (int i = 0; i < argc; i++) {
        char* arg = argv[i];

        if (strcmp("-S", arg) == 0 || strcmp("--seed", arg) == 0) {
            seed = strtoull(argv[i + 1], NULL, 16);
            i++;
        }
    }

    printf("Using seed: %016llx\n", seed);
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
            printf("PASSED");
            break;
        case CN_TEST_FAIL:
            failed++;
            printf("FAILED");
            break;
        case CN_TEST_GEN_FAIL:
            errored++;
            printf("FAILED TO GENERATE VALID INPUT");
            break;
        case CN_TEST_SKIP:
            skipped++;
            printf("SKIPPED");
            break;
        }
        printf("\n");
    }

    printf("\nTesting Summary:\n");
    printf(
        "cases: %d, passed: %d, failed: %d, errored: %d, skipped: %d\n",
        num_test_cases, passed, failed, errored, skipped);

    return !(failed == 0 && errored == 0);
}
