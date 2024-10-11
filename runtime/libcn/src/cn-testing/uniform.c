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

SIGNED_GEN(8);
SIGNED_GEN(16);
SIGNED_GEN(32);
SIGNED_GEN(64);

#define BITS_GEN(sm)                                                                    \
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
uint##sm##_t range_u##sm(uint##sm##_t min, uint##sm##_t max) {                          \
    uint##sm##_t x = uniform_u##sm(max - min);                                          \
    return x + min;                                                                     \
}                                                                                       \
int##sm##_t range_i##sm(int##sm##_t min, int##sm##_t max) {                             \
    return range_u##sm(min, max);                                                       \
}                                                                                       \
cn_bits_u##sm* cn_gen_range_cn_bits_u##sm(cn_bits_u##sm* min, cn_bits_u##sm* max) {     \
    return convert_to_cn_bits_u##sm(range_u##sm(min->val, max->val));                   \
}                                                                                       \
cn_bits_i##sm* cn_gen_range_cn_bits_i##sm(cn_bits_i##sm* min, cn_bits_i##sm* max) {     \
    return convert_to_cn_bits_i##sm(range_i##sm(min->val, max->val));                   \
}

RANGE_GEN(8);
RANGE_GEN(16);
RANGE_GEN(32);
RANGE_GEN(64);

#define INEQ_GEN(sm)\
uint##sm##_t lt_u##sm(uint##sm##_t max) {                                               \
    return range_u##sm(0, max);                                                         \
}                                                                                       \
int##sm##_t lt_i##sm(int##sm##_t max) {                                                 \
    return range_i##sm(INT##sm##_MIN, max);                                             \
}                                                                                       \
cn_bits_u##sm* cn_gen_lt_cn_bits_u##sm(cn_bits_u##sm* max) {                            \
    return convert_to_cn_bits_u##sm(lt_u##sm(max->val));                                \
}                                                                                       \
cn_bits_i##sm* cn_gen_lt_cn_bits_i##sm(cn_bits_i##sm* max) {                            \
    return convert_to_cn_bits_i##sm(lt_i##sm(max->val));                                \
}                                                                                       \
uint##sm##_t ge_u##sm(uint##sm##_t min) {                                               \
    return range_u##sm(min, 0);                                                         \
}                                                                                       \
int##sm##_t ge_i##sm(int##sm##_t min) {                                                 \
    return range_i##sm(min, INT##sm##_MIN);                                             \
}                                                                                       \
cn_bits_u##sm* cn_gen_ge_cn_bits_u##sm(cn_bits_u##sm* min) {                            \
    return convert_to_cn_bits_u##sm(ge_u##sm(min->val));                                \
}                                                                                       \
cn_bits_i##sm* cn_gen_ge_cn_bits_i##sm(cn_bits_i##sm* min) {                            \
    return convert_to_cn_bits_i##sm(ge_i##sm(min->val));                                \
}

INEQ_GEN(8);
INEQ_GEN(16);
INEQ_GEN(32);
INEQ_GEN(64);

#define MULT_RANGE_GEN(sm)                                                              \
uint##sm##_t mult_range_u##sm(                                                          \
    uint##sm##_t mul,                                                                   \
    uint##sm##_t min,                                                                   \
    uint##sm##_t max                                                                    \
) {                                                                                     \
    assert(mul != 0);                                                                   \
    uint##sm##_t x = range_u##sm(min / mul, max / mul + (max % mul != 0));              \
    return x * mul;                                                                     \
}                                                                                       \
int##sm##_t mult_range_i##sm(                                                           \
    int##sm##_t mul,                                                                    \
    int##sm##_t min,                                                                    \
    int##sm##_t max                                                                     \
) {                                                                                     \
    assert(mul != 0);                                                                   \
    int##sm##_t x = range_i##sm(min / mul, max / mul + (max % mul != 0));               \
    return x * mul;                                                                     \
}                                                                                       \
cn_bits_u##sm* cn_gen_mult_range_cn_bits_u##sm(                                         \
    cn_bits_u##sm* mul,                                                                 \
    cn_bits_u##sm* min,                                                                 \
    cn_bits_u##sm* max                                                                  \
) {                                                                                     \
    return convert_to_cn_bits_u##sm(mult_range_u##sm(mul->val, min->val, max->val));    \
}                                                                                       \
cn_bits_i##sm* cn_gen_mult_range_cn_bits_i##sm(                                         \
    cn_bits_i##sm* mul,                                                                 \
    cn_bits_i##sm* min,                                                                 \
    cn_bits_i##sm* max                                                                  \
) {                                                                                     \
    return convert_to_cn_bits_i##sm(mult_range_i##sm(mul->val, min->val, max->val));    \
}

MULT_RANGE_GEN(8);
MULT_RANGE_GEN(16);
MULT_RANGE_GEN(32);
MULT_RANGE_GEN(64);

#define MULT_GEN(sm)                                                                    \
uint##sm##_t mult_u##sm(uint##sm##_t mul) {                                             \
    return mult_range_u##sm(mul, 0, UINT##sm##_MAX);                                    \
}                                                                                       \
int##sm##_t mult_i##sm(int##sm##_t mul) {                                               \
    return mult_range_i##sm(mul, INT##sm##_MIN, INT##sm##_MAX);                         \
}\
cn_bits_u##sm* cn_gen_mult_cn_bits_u##sm(cn_bits_u##sm* mul) {                          \
    return convert_to_cn_bits_u##sm(mult_u##sm(mul->val));                              \
}                                                                                       \
cn_bits_i##sm* cn_gen_mult_cn_bits_i##sm(cn_bits_i##sm* mul) {                          \
    return convert_to_cn_bits_i##sm(mult_i##sm(mul->val));                              \
}

MULT_GEN(8);
MULT_GEN(16);
MULT_GEN(32);
MULT_GEN(64);
