#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <cn-testing/rand.h>

// Mersenne twister from https://doi.org/10.1145/369534.369540

/* Period parameters */
#define NN 312
#define M0 63
#define M1 151
#define M2 224
/* Constant vector a */
#define MATRIX_A 0xB3815B624FC82E2FULL
/* Most significant 33 bits */
#define UMASK 0xFFFFFFFF80000000ULL
/* Least significant 31 bits */
#define LMASK 0x7FFFFFFFULL

/* Tempering parameters */
#define MASK_B 0x599CFCBFCA660000ULL
#define MASK_C 0xFFFAAFFE00000000ULL
#define UU 26
#define SS 17
#define TT 33
#define LL 39

/* The array for the state vector */
static unsigned long long mt[NN];
/* mti55NN11 means mt[NN] is not initialized */
static int mti = NN + 1;

void sgenrand(uint64_t seed)
{
    uint64_t ux, lx;
    for (mti = 0; mti < NN; mti++) {
        ux = seed & 0xFFFFFFFF00000000ULL;
        seed = 2862933555777941757ULL * seed + 1ULL;
        lx = seed >> 32;
        seed = 2862933555777941757ULL * seed + 1ULL;
        mt[mti] = ux | lx;
    }
}

uint64_t genrand(void) {
    int32_t i;
    uint64_t x;
    static unsigned long long mag01[2] = { 0ULL,MATRIX_A };

    if (mti >= NN) {/* generate NN words at one time */
        /* if sgenrand() has not been called, */
        /* a default initial seed is used */
        if (mti == NN + 1) sgenrand(0xDEADCAFE);

        for (i = 0;i < NN - M2;i++) {
            x = (mt[i] & UMASK) | (mt[i + 1] & LMASK);
            mt[i] = (x >> 1) ^ mag01[(int)(x & 1ULL)];
            mt[i] ^= mt[i + M0] ^ mt[i + M1] ^ mt[i + M2];
        }
        for (;i < NN - M1;i++) {
            x = (mt[i] & UMASK) | (mt[i + 1] & LMASK);
            mt[i] = (x >> 1) ^ mag01[(int)(x & 1ULL)];
            mt[i] ^= mt[i + M0] ^ mt[i + M1] ^ mt[i + M2 - NN];
        }
        for (;i < NN - M0;i++) {
            x = (mt[i] & UMASK) | (mt[i + 1] & LMASK);
            mt[i] = (x >> 1) ^ mag01[(int)(x & 1ULL)];
            mt[i] ^= mt[i + M0] ^ mt[i + M1 - NN] ^ mt[i + M2 - NN];
        }
        for (;i < NN - 1;i++) {
            x = (mt[i] & UMASK) | (mt[i + 1] & LMASK);
            mt[i] = (x >> 1) ^ mag01[(int)(x & 1ULL)];
            mt[i] ^= mt[i + M0 - NN] ^ mt[i + M1 - NN] ^ mt[i + M2 - NN];
        }
        x = (mt[NN - 1] & UMASK) | (mt[0] & LMASK);
        mt[NN - 1] = (x >> 1) ^ mag01[(int)(x & 1ULL)];
        mt[NN - 1] ^= mt[M0 - 1] ^ mt[M1 - 1] ^ mt[M2 - 1];

        mti = 0;
    }

    x = mt[mti++];
    x ^= (x >> UU);
    x ^= (x << SS) & MASK_B;
    x ^= (x << TT) & MASK_C;
    x ^= (x >> LL);

    return x;
}

/////////////////////////////
// End of Mersenne twister //
/////////////////////////////

// Sized generation according to Lemire: https://doi.org/10.1145/3230636
#define UNSIGNED_GEN(sm, lg)                                                            \
uint##sm##_t cn_gen_uniform_u##sm(uint##sm##_t s) {                                     \
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
uint64_t cn_gen_uniform_u64(uint64_t s) {
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
int##sm##_t cn_gen_uniform_i##sm(uint##sm##_t s) {                                      \
    uint##sm##_t x = cn_gen_uniform_u##sm(s);                                           \
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

#define RANGE_GEN(sm)                                                                   \
uint##sm##_t cn_gen_range_u##sm(uint##sm##_t min, uint##sm##_t max) {                   \
    uint##sm##_t x = cn_gen_uniform_u##sm(max - min);                                   \
    return x + min;                                                                     \
}                                                                                       \
int##sm##_t cn_gen_range_i##sm(int##sm##_t min, int##sm##_t max) {                      \
    return cn_gen_range_u##sm(min, max);                                                \
}

RANGE_GEN(8);
RANGE_GEN(16);
RANGE_GEN(32);
RANGE_GEN(64);

#define INEQ_GEN(sm)\
uint##sm##_t cn_gen_lt_u##sm(uint##sm##_t max) {                                        \
    return cn_gen_range_u##sm(0, max);                                                  \
}                                                                                       \
int##sm##_t cn_gen_lt_i##sm(int##sm##_t max) {                                          \
    return cn_gen_range_i##sm(INT##sm##_MIN, max);                                      \
}                                                                                       \
uint##sm##_t cn_gen_ge_u##sm(uint##sm##_t min) {                                        \
    return cn_gen_range_u##sm(min, 0);                                                  \
}                                                                                       \
int##sm##_t cn_gen_ge_i##sm(int##sm##_t min) {                                          \
    return cn_gen_range_i##sm(min, INT##sm##_MIN);                                      \
}

INEQ_GEN(8);
INEQ_GEN(16);
INEQ_GEN(32);
INEQ_GEN(64);

#define MULT_RANGE_GEN(sm)                                                              \
uint##sm##_t cn_gen_mult_range_u##sm(                                                   \
    uint##sm##_t mul,                                                                   \
    uint##sm##_t min,                                                                   \
    uint##sm##_t max                                                                    \
) {                                                                                     \
    assert(mul != 0);                                                                   \
    uint##sm##_t x = cn_gen_range_u##sm(min / mul, max / mul + (max % mul != 0));       \
    return x * mul;                                                                     \
}                                                                                       \
int##sm##_t cn_gen_mult_range_i##sm(                                                    \
    int##sm##_t mul,                                                                    \
    int##sm##_t min,                                                                    \
    int##sm##_t max                                                                     \
) {                                                                                     \
    assert(mul != 0);                                                                   \
    int##sm##_t x = cn_gen_range_i##sm(min / mul, max / mul + (max % mul != 0));        \
    return x * mul;                                                                     \
}

MULT_RANGE_GEN(8);
MULT_RANGE_GEN(16);
MULT_RANGE_GEN(32);
MULT_RANGE_GEN(64);

#define MULT_GEN(sm)                                                                    \
uint##sm##_t cn_gen_mult_u##sm(uint##sm##_t mul) {                                      \
    return cn_gen_mult_range_u##sm(mul, 0, UINT##sm##_MAX);                             \
}                                                                                       \
int##sm##_t cn_gen_mult_i##sm(int##sm##_t mul) {                                        \
    return cn_gen_mult_range_i##sm(mul, INT##sm##_MIN, INT##sm##_MAX);                  \
}

MULT_GEN(8);
MULT_GEN(16);
MULT_GEN(32);
MULT_GEN(64);

void cn_gen_shuffle(void* arr, size_t len, size_t size) {
    // byte size is implementation-defined (6.5.3.4, bullet 2)
    // but `sizeof(char) == 1` is guaranteed.
    char tmp[size];
    char* p = arr;

    for (int i = len - 1; i >= 0; i--) {
        uint8_t j = cn_gen_range_u8(0, i + 1);
        memcpy(tmp, arr + i * size, size);
        memcpy(arr + i * size, arr + j * size, size);
        memcpy(arr + j * size, tmp, size);
    }
}

static int comp_size_t(const void* x, const void* y) {
    size_t a = *(const size_t*)x;
    size_t b = *(const size_t*)y;

    if (a < b) return -1;
    if (b > a) return 1;
    return 0;
}

void cn_gen_split(size_t n, size_t* arr[], size_t len) {
    if (len == 1) {
        *(arr[0]) = n;
        return;
    }

    if (len == 2) {
        *(arr[0]) = (size_t)cn_gen_range_u64(0, n + 1);
        *(arr[1]) = n - *(arr[0]);
        return;
    }

    int used = 0;
    for (int i = 0; i < len - 1; i++) {
        int left = n - (len - i) + 1 - used;
        size_t rnd = (size_t)cn_gen_range_u64(1, left + 1);
        *(arr[i]) = rnd;
        used += rnd;
    }
    *(arr[len - 1]) = n - 1 - used;

    cn_gen_shuffle(&arr, len, sizeof(size_t*));
}

struct choice_list {
    uint64_t choice;
    struct choice_list* next;
    struct choice_list* prev;
};

static struct choice_list* choice_history = 0;

void cn_gen_srand(uint64_t seed) {
    sgenrand(seed);

    while (choice_history != 0) {
        struct choice_list* tmp = choice_history;
        choice_history = choice_history->next;
        free(tmp);
    }
}

uint64_t cn_gen_rand(void) {
    if (choice_history != 0 && choice_history->next != 0)
    {
        choice_history = choice_history->next;
        return choice_history->choice;
    }
    else
    {
        uint64_t choice = genrand();

        struct choice_list* new_node = malloc(sizeof(struct choice_list));
        *new_node = (struct choice_list){
            .choice = choice,
            .next = 0,
            .prev = choice_history
        };

        if (choice_history != 0) {
            assert(choice_history->next == 0);
            choice_history->next = new_node;
        }

        choice_history = new_node;

        return choice;
    }
}

uint64_t cn_gen_rand_retry() {
    uint64_t choice = genrand();

    struct choice_list* next = (choice_history != 0) ? choice_history->next : 0;
    struct choice_list* prev = (choice_history != 0) ? choice_history->prev : 0;

    struct choice_list* new_node = malloc(sizeof(struct choice_list));
    *new_node = (struct choice_list){
        .choice = choice,
        .next = next,
        .prev = prev
    };

    choice_history = new_node;

    return choice;
}

cn_gen_rand_checkpoint cn_gen_rand_save(void) {
    assert(choice_history != 0);
    return choice_history;
}

void cn_gen_rand_restore(cn_gen_rand_checkpoint checkpoint) {
    choice_history = checkpoint;
}

void free_list(struct choice_list* curr) {
    while (curr != NULL) {
        struct choice_list* tmp = curr;
        curr = curr->next;
        free(tmp);
    }
}

void cn_gen_rand_replace(cn_gen_rand_checkpoint checkpoint) {
    cn_gen_rand_restore(checkpoint);
    free_list(choice_history->next);
    choice_history->next = 0;
}
