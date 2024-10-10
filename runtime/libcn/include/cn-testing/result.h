#ifndef CN_TEST_RESULT_H
#define CN_TEST_RESULT_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

    typedef uint64_t seed;

    enum cn_test_result {
        CN_TEST_PASS,
        CN_TEST_FAIL,
        CN_TEST_GEN_FAIL,
        CN_TEST_SKIP
    };

#ifdef __cplusplus
}
#endif

#endif // CN_TEST_RESULT_H
