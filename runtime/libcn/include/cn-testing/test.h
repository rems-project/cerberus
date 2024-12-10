#ifndef CN_TEST_H
#define CN_TEST_H

#include <setjmp.h>
#include <cn-executable/utils.h>
#include <cn-testing/uniform.h>
#include <cn-testing/result.h>

typedef enum cn_test_result cn_test_case_fn(int);

void cn_register_test_case(char* suite, char* name, cn_test_case_fn* func);

void print_test_info(char* suite, char* name, int tests, int discards);

#define CN_UNIT_TEST_CASE(Name)                                                         \
    static jmp_buf buf_##Name;                                                          \
                                                                                        \
    void cn_test_##Name##_fail () {                                                     \
        longjmp(buf_##Name, 1);                                                         \
    }                                                                                   \
                                                                                        \
    enum cn_test_result cn_test_##Name () {                                             \
        if (setjmp(buf_##Name)) {                                                       \
            return CN_TEST_FAIL;                                                        \
        }                                                                               \
        set_cn_failure_cb(&cn_test_##Name##_fail);                                      \
                                                                                        \
        CN_TEST_INIT();                                                                 \
        Name();                                                                         \
                                                                                        \
        return CN_TEST_PASS;                                                            \
    }

#define CN_RANDOM_TEST_CASE_WITH_CUSTOM_INIT(Suite, Name, Samples, Init, ...)           \
    static jmp_buf buf_##Name;                                                          \
                                                                                        \
    void cn_test_##Name##_fail (enum cn_failure_mode mode) {                            \
        longjmp(buf_##Name, mode);                                                      \
    }                                                                                   \
                                                                                        \
    enum cn_test_result cn_test_##Name (int printing) {                                 \
        cn_gen_rand_checkpoint checkpoint = cn_gen_rand_save();                         \
        int i = 0, d = 0;                                                               \
        set_cn_failure_cb(&cn_test_##Name##_fail);                                      \
        switch (setjmp(buf_##Name)) {                                                   \
            case CN_FAILURE_ASSERT:                                                     \
            case CN_FAILURE_CHECK_OWNERSHIP:                                            \
            case CN_FAILURE_OWNERSHIP_LEAK:                                             \
                return CN_TEST_FAIL;                                                    \
            case CN_FAILURE_ALLOC:                                                      \
                cn_gen_rand_replace(checkpoint);                                        \
                d++;                                                                    \
                break;                                                                  \
        }                                                                               \
        for (; i < Samples; i++) {                                                      \
            if (printing) {                                                             \
                printf("\r");                                                           \
                print_test_info(#Suite, #Name, i, d);                                   \
            }                                                                           \
            if (d == 10 * Samples) {                                                    \
                return CN_TEST_GEN_FAIL;                                                \
            }                                                                           \
            size_t sz = cn_gen_uniform_cn_bits_u16(cn_gen_get_max_size())->val + 1;     \
            cn_gen_set_size(sz);                                                        \
            CN_TEST_INIT();                                                             \
            cn_gen_set_input_timer(cn_gen_get_milliseconds());                          \
            struct cn_gen_##Name##_record *res = cn_gen_##Name();                       \
            if (cn_gen_backtrack_type() != CN_GEN_BACKTRACK_NONE) {                     \
                cn_gen_rand_replace(checkpoint);                                        \
                i--;                                                                    \
                d++;                                                                    \
                continue;                                                               \
            }                                                                           \
            assume_##Name(__VA_ARGS__);                                                 \
            Init(res);                                                                  \
            Name(__VA_ARGS__);                                                          \
            cn_gen_rand_replace(checkpoint);                                            \
        }                                                                               \
                                                                                        \
        if (printing) {                                                                 \
            printf("\r");                                                               \
            print_test_info(#Suite, #Name, i, d);                                       \
        }                                                                               \
        return CN_TEST_PASS;                                                            \
    }

#define CN_RANDOM_TEST_CASE_WITH_INIT(Suite, Name, Samples, ...)                        \
    CN_RANDOM_TEST_CASE_WITH_CUSTOM_INIT(                                               \
        Suite, Name, Samples, cn_test_##Name##_init, __VA_ARGS__)


#define CN_RANDOM_TEST_CASE(Suite, Name, Samples, ...)                                  \
    CN_RANDOM_TEST_CASE_WITH_CUSTOM_INIT(Suite, Name, Samples, , __VA_ARGS__)

int cn_test_main(int argc, char* argv[]);

#define CN_TEST_INIT()                                                                  \
    free_all();                                                                         \
    reset_error_msg_info();                                                             \
    initialise_ownership_ghost_state();                                                 \
    initialise_ghost_stack_depth();                                                     \
    cn_gen_backtrack_reset();                                                           \
    cn_gen_alloc_reset();                                                               \
    cn_gen_ownership_reset();

#define CN_TEST_GENERATE(name) ({                                                       \
    struct cn_gen_##name##_record* res = cn_gen_##name();                               \
    if (cn_gen_backtrack_type() != CN_GEN_BACKTRACK_NONE) {                             \
        printf("generation failed\n");                                                  \
        return 1;                                                                       \
    }                                                                                   \
    res;                                                                                \
})

#endif // CN_TEST_H
