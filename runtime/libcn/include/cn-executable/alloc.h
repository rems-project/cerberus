#ifndef CN_ALLOC
#define CN_ALLOC

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif



void* cn_alloc(size_t nbytes);

void* cn_zalloc(size_t nbytes);

void cn_free_all();

typedef uintptr_t cn_alloc_checkpoint;

cn_alloc_checkpoint cn_alloc_save_checkpoint(void);

void cn_free_after(cn_alloc_checkpoint ptr);

#ifdef __cplusplus
}
#endif

#endif // CN_ALLOC
