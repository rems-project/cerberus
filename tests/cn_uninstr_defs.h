#include <stdio.h>
#include <stdlib.h>

void *cn_aligned_alloc(size_t align, size_t size);
void *cn_malloc(unsigned long size);
void *cn_calloc(size_t num, size_t size);
void cn_print_u64(const char * x, unsigned long y);
void cn_print_nr_u64(int x, unsigned long y);
void cn_free_sized(void* malloced_ptr, size_t size);
void cn_print_nr_owned_predicates(void);