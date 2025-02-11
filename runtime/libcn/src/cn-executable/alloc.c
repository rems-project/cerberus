#include <stdio.h>
#include <stdlib.h>
#include <stdalign.h>
#include <string.h>

#include <cn-executable/alloc.h>
#include <cn-executable/utils.h>



#define MEM_SIZE (1024 * 1024 * 1024)
char buf[MEM_SIZE];
static char* curr = buf;

// 268,435,449

void* _cn_aligned_alloc(size_t alignment, size_t nbytes) {
    size_t max = (uintptr_t)buf + MEM_SIZE;

    if ((uintptr_t)curr % alignment != 0) {
        size_t padding = (alignment - (uintptr_t)curr % alignment) % alignment;
        if ((uintptr_t)curr + padding >= max) {
            cn_failure(CN_FAILURE_ALLOC);
            return NULL;
        }
        curr += padding;
    }

    void* res = curr;
    if ((uintptr_t)curr + nbytes > max) {
        cn_failure(CN_FAILURE_ALLOC);
        return NULL;
    }
    curr += nbytes;

    return res;
}

void* cn_alloc(size_t nbytes) {
    return _cn_aligned_alloc(alignof(max_align_t), nbytes);
}

void* cn_zalloc(size_t nbytes) {
    void* p = cn_alloc(nbytes);
    if (p != NULL) {
        memset(p, 0, nbytes);
    }
    return p;
}

void cn_free_all(void) {
    curr = buf;
}

cn_alloc_checkpoint cn_alloc_save_checkpoint(void) {
    return (uintptr_t)curr;
}

void cn_free_after(cn_alloc_checkpoint ptr) {
    curr = (char*)ptr;
}
