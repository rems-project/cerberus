#ifndef CN_GEN_RAND_H
#define CN_GEN_RAND_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

    void cn_gen_set_rand_inject(uint8_t inject);

    void cn_gen_srand(uint64_t seed);

    uint64_t cn_gen_rand(void);

    uint64_t cn_gen_rand_retry(void);

    typedef void* cn_gen_rand_checkpoint;

    cn_gen_rand_checkpoint cn_gen_rand_save(void);

    void cn_gen_rand_restore(cn_gen_rand_checkpoint checkpoint);

#ifdef __cplusplus
}
#endif

#endif // CN_GEN_RAND_H
