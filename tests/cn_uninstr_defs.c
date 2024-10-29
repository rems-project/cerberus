#include "cn_uninstr_defs.h"

#ifndef CN_UTILS
void *cn_aligned_alloc(size_t align, size_t size) {
    return aligned_alloc(align, size);
}
void *cn_malloc(unsigned long size) {
    return malloc(size);
}
void *cn_calloc(size_t num, size_t size) {
    return calloc(num, size);
}
void cn_print_u64(const char * x, unsigned long y) {
    printf("%lu\n", y);
}
void cn_print_nr_u64(int x, unsigned long y) {
    printf("%lu\n", y);
}
void cn_free_sized(void* malloced_ptr, size_t size) {
    return;
}
void cn_print_nr_owned_predicates(void) {
    return;
}
#endif