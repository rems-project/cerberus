#include <stdint.h>
#include <stdlib.h>
#include <assert.h>

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

static uint8_t cn_gen_rand_inject = 0;

void cn_gen_set_rand_inject(uint8_t inject) {
    cn_gen_rand_inject = inject;
}

uint64_t rand_normal(void) {
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

uint64_t rand_inject() {
    uint64_t choice = genrand();

    struct choice_list* next = (choice_history != 0) ? choice_history->next : 0;

    struct choice_list* new_node = malloc(sizeof(struct choice_list));
    *new_node = (struct choice_list){
        .choice = choice,
        .next = next,
        .prev = choice_history
    };

    choice_history = new_node;

    return choice;
}

uint64_t cn_gen_rand() {
    if (cn_gen_rand_inject) {
        return rand_inject();
    }
    else
    {
        return rand_normal();
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
