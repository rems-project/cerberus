#ifndef CN_TEST_H
#define CN_TEST_H

#include <setjmp.h>
#include <cn-executable/utils.h>
#include <cn-testing/result.h>

typedef enum cn_test_result cn_test_case_fn(void);

void cn_register_test_case(char* suite, char* name, cn_test_case_fn* func);

#define CN_TEST_CASE(Suite, Name, Samples, ...)                                         \
    static jmp_buf buf_##Suite##_##Name;                                                \
                                                                                        \
    void cn_test_##Suite##_##Name##_fail () {                                           \
        longjmp(buf_##Suite##_##Name, 1);                                               \
    }                                                                                   \
                                                                                        \
    enum cn_test_result cn_test_##Suite##_##Name () {                                   \
        if (setjmp(buf_##Suite##_##Name)) {                                             \
            return CN_TEST_FAIL;                                                        \
        }                                                                               \
        set_cn_exit_cb(&cn_test_##Suite##_##Name##_fail);                               \
                                                                                        \
        for (int i = 0; i < Samples; i++) {                                             \
            CN_TEST_INIT();                                                             \
            struct cn_gen_##Name##_record *res = cn_gen_##Name();                       \
            if (cn_gen_backtrack_type() != CN_GEN_BACKTRACK_NONE) {                     \
                return CN_TEST_GEN_FAIL;                                                \
            }                                                                           \
            Name(__VA_ARGS__);                                                          \
        }                                                                               \
                                                                                        \
        return CN_TEST_PASS;                                                            \
    }

int cn_test_main(int argc, char* argv[]);

#define CN_TEST_INIT()                                                                  \
    free_all();                                                                         \
    initialise_ownership_ghost_state();                                                 \
    initialise_ghost_stack_depth();                                                     \
    cn_gen_alloc_reset();

#define CN_TEST_GENERATE(name) ({                                                       \
    struct cn_gen_##name##_record* res = cn_gen_##name();                               \
    if (cn_gen_backtrack_type() != CN_GEN_BACKTRACK_NONE) {                             \
        printf("generation failed\n");                                                  \
        return 1;                                                                       \
    }                                                                                   \
    res;                                                                                \
})

#endif // CN_TEST_H
