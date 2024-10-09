#include "assert.h"

#include <cn-executable/utils.h>
#include <cn-testing/rand.h>
#include <cn-testing/uniform.h>

// Sized generation according to Lemire: https://doi.org/10.1145/3230636
#define UNSIGNED_GEN(sm, lg)                                                            \
static uint##sm##_t uniform_u##sm(uint##sm##_t s) {                                     \
    uint##sm##_t x = cn_gen_rand();                                                     \
    if (s == 0) {                                                                       \
        return x;                                                                       \
    }                                                                                   \
                                                                                        \
    uint##lg##_t m = (uint##lg##_t)x * (uint##lg##_t)s;                                 \
    uint##sm##_t l = m; /* m % pow(2, sm) */                                            \
    if (l < s) {                                                                        \
        uint##lg##_t t = (UINT##sm##_MAX - (s - 1)) % s;                                \
        while (l < t) {                                                                 \
            x = cn_gen_rand();                                                          \
            m = x * s;                                                                  \
            l = m; /* m % pow(2, sm) */                                                 \
        }                                                                               \
    }                                                                                   \
    return m >> sm;                                                                     \
}

UNSIGNED_GEN(8, 16);
UNSIGNED_GEN(16, 32);
UNSIGNED_GEN(32, 64);

// OpenJDK 9 implementation, according to the definition in Lemire.
static uint64_t uniform_u64(uint64_t s) {
    uint64_t x = cn_gen_rand();
    if (s == 0) {
        return x;
    }

    uint64_t r = x % s;
    while (x - r > UINT64_MAX - (s - 1)) {
        x = cn_gen_rand();
        r = x % s;
    }
    return r;
}

#define SIGNED_GEN(sm)                                                                  \
static int##sm##_t uniform_i##sm(uint##sm##_t s) {                                      \
    uint##sm##_t x = uniform_u##sm(s);                                                  \
    if (s == 0) {                                                                       \
        return x;                                                                       \
    }                                                                                   \
    uint##sm##_t offset = (s + 1) >> 2;                                                 \
    return x - offset;                                                                  \
}


#define BITS_GEN(sm)                                                                    \
SIGNED_GEN(sm);                                                                         \
                                                                                        \
cn_bits_u##sm* cn_gen_uniform_cn_bits_u##sm(uint64_t sz) {                              \
    return convert_to_cn_bits_u##sm(uniform_u##sm(sz));                                 \
}                                                                                       \
                                                                                        \
cn_bits_i##sm* cn_gen_uniform_cn_bits_i##sm(uint64_t sz) {                              \
    return convert_to_cn_bits_i##sm(uniform_i##sm(sz));                                 \
}

BITS_GEN(8);
BITS_GEN(16);
BITS_GEN(32);
BITS_GEN(64);

#define RANGE_GEN(sm)                                                                   \
cn_bits_u##sm* cn_gen_range_cn_bits_u##sm(cn_bits_u##sm* min, cn_bits_u##sm* max) {     \
    uint##sm##_t x = uniform_u##sm(max->val - min->val);                                \
    return convert_to_cn_bits_u##sm(x + min->val);                                      \
}                                                                                       \
cn_bits_i##sm* cn_gen_range_cn_bits_i##sm(cn_bits_i##sm* min, cn_bits_i##sm* max) {     \
    uint##sm##_t x = uniform_u##sm((uint##sm##_t)max->val - (uint##sm##_t)min->val);    \
    return convert_to_cn_bits_i##sm(x + (uint##sm##_t)min->val);                        \
}

RANGE_GEN(8);
RANGE_GEN(16);
RANGE_GEN(32);
RANGE_GEN(64);
