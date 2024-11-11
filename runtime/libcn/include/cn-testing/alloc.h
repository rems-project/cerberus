#ifndef CN_GEN_ALLOC_H
#define CN_GEN_ALLOC_H

#include <stdlib.h>

#include <cn-executable/utils.h>

#ifdef __cplusplus
extern "C" {
#endif

    uint8_t get_null_in_every(void);
    void set_null_in_every(uint8_t n);

    int is_sized_null(void);
    void set_sized_null(void);
    void unset_sized_null(void);

    void cn_gen_alloc_reset(void);
    void* cn_gen_alloc_save(void);
    void cn_gen_alloc_restore(void* ptr);

    void cn_gen_ownership_reset(void);

    void* cn_gen_ownership_save(void);

    void cn_gen_ownership_restore(void* ptr);

    cn_pointer* cn_gen_alloc(cn_bits_u64* sz);

    cn_pointer* cn_gen_aligned_alloc(cn_bits_u64* alignment, cn_bits_u64* sz);

    int cn_gen_alloc_check(void* p, size_t sz);

    void cn_gen_ownership_update(void* p, size_t sz);

    int cn_gen_ownership_check(void* p, size_t sz);

#ifdef __cplusplus
}
#endif

#endif // CN_GEN_ALLOC_H
