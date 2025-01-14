#ifndef CN_TEST_H
#define CN_TEST_H

#include <setjmp.h>
#include <cn-executable/utils.h>
#include <cn-testing/uniform.h>
#include <cn-testing/result.h>

enum cn_test_gen_progress {
    CN_TEST_GEN_PROGRESS_NONE = 0,
    CN_TEST_GEN_PROGRESS_FINAL = 1,
    CN_TEST_GEN_PROGRESS_ALL = 2
};

typedef enum cn_test_result cn_test_case_fn(enum cn_test_gen_progress);

void cn_register_test_case(const char* suite, const char* name, cn_test_case_fn* func);

void print_test_info(const char* suite, const char* name, int tests, int discards);


#define CN_UNIT_TEST_CASE_NAME(FuncName) cn_test_const_##FuncName

#define CN_UNIT_TEST_CASE(FuncName)                                                     \
    static jmp_buf buf_##FuncName;                                                      \
                                                                                        \
    void cn_test_const_##FuncName##_fail () {                                           \
        longjmp(buf_##FuncName, 1);                                                     \
    }                                                                                   \
                                                                                        \
    enum cn_test_result cn_test_const_##FuncName () {                                   \
        if (setjmp(buf_##FuncName)) {                                                   \
            return CN_TEST_FAIL;                                                        \
        }                                                                               \
        set_cn_failure_cb(&cn_test_const_##FuncName##_fail);                            \
                                                                                        \
        CN_TEST_INIT();                                                                 \
        FuncName();                                                                     \
                                                                                        \
        return CN_TEST_PASS;                                                            \
    }

#define CN_REGISTER_UNIT_TEST_CASE(Suite, FuncName)                                     \
    cn_register_test_case(                                                              \
        #Suite,                                                                         \
        #FuncName,                                                                      \
        &CN_UNIT_TEST_CASE_NAME(FuncName));

#define CN_RANDOM_TEST_CASE_WITH_CUSTOM_INIT(Suite, Name, Samples, Init, ...)           \
    static jmp_buf buf_##Name;                                                          \
                                                                                        \
    void cn_test_gen_##Name##_fail (enum cn_failure_mode mode) {                        \
        longjmp(buf_##Name, mode);                                                      \
    }                                                                                   \
                                                                                        \
    enum cn_test_result cn_test_gen_##Name (enum cn_test_gen_progress progress_level) { \
        cn_gen_rand_checkpoint checkpoint = cn_gen_rand_save();                         \
        int i = 0, d = 0;                                                               \
        set_cn_failure_cb(&cn_test_gen_##Name##_fail);                                  \
        switch (setjmp(buf_##Name)) {                                                   \
            case CN_FAILURE_ASSERT:                                                     \
            case CN_FAILURE_CHECK_OWNERSHIP:                                            \
            case CN_FAILURE_OWNERSHIP_LEAK:                                             \
                if (progress_level == CN_TEST_GEN_PROGRESS_FINAL) {                     \
                    print_test_info(#Suite, #Name, i, d);                               \
                }                                                                       \
                return CN_TEST_FAIL;                                                    \
            case CN_FAILURE_ALLOC:                                                      \
                cn_gen_rand_replace(checkpoint);                                        \
                d++;                                                                    \
                break;                                                                  \
        }                                                                               \
        for (; i < Samples; i++) {                                                      \
            if (progress_level == CN_TEST_GEN_PROGRESS_ALL) {                           \
                printf("\r");                                                           \
                print_test_info(#Suite, #Name, i, d);                                   \
            }                                                                           \
            if (d == 10 * Samples) {                                                    \
                if (progress_level == CN_TEST_GEN_PROGRESS_FINAL) {                     \
                    print_test_info(#Suite, #Name, i, d);                               \
                }                                                                       \
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
        if (progress_level != CN_TEST_GEN_PROGRESS_NONE) {                              \
            if (progress_level == CN_TEST_GEN_PROGRESS_ALL) {                           \
                printf("\r");                                                           \
            }                                                                           \
            print_test_info(#Suite, #Name, i, d);                                       \
        }                                                                               \
        return CN_TEST_PASS;                                                            \
    }

#define CN_RANDOM_TEST_CASE_WITH_INIT(Suite, Name, Samples, ...)                        \
    CN_RANDOM_TEST_CASE_WITH_CUSTOM_INIT(                                               \
        Suite, Name, Samples, cn_test_gen_##Name##_init, __VA_ARGS__)


#define CN_RANDOM_TEST_CASE_NAME(FuncName) cn_test_gen_##FuncName

#define CN_RANDOM_TEST_CASE(Suite, Name, Samples, ...)                                  \
    CN_RANDOM_TEST_CASE_WITH_CUSTOM_INIT(Suite, Name, Samples, , __VA_ARGS__)

#define CN_REGISTER_RANDOM_TEST_CASE(Suite, FuncName)                                   \
    cn_register_test_case(                                                              \
        #Suite,                                                                         \
        #FuncName,                                                                      \
        &CN_RANDOM_TEST_CASE_NAME(FuncName));

int cn_test_main(int argc, char* argv[]);

#define CN_TEST_INIT()                                                                  \
    free_all();                                                                         \
    reset_error_msg_info();                                                             \
    initialise_ownership_ghost_state();                                                 \
    initialise_ghost_stack_depth();                                                     \
    cn_gen_backtrack_reset();                                                           \
    cn_gen_alloc_reset();                                                               \
    cn_gen_ownership_reset();

#endif // CN_TEST_H
