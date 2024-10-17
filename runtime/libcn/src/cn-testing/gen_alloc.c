#include "stdlib.h"

#include <cn-executable/utils.h>

#include <cn-testing/prelude.h>

static hash_table* pointer_size_map = 0;

void cn_gen_alloc_reset(void) {
    pointer_size_map = ht_create();
}

cn_pointer* cn_gen_alloc(cn_bits_u64* sz) {
    uint64_t bytes = convert_from_cn_bits_u64(sz);
    if (cn_gen_backtrack_type() == CN_GEN_BACKTRACK_ALLOC) {
        bytes = cn_gen_backtrack_alloc_get();
        cn_gen_backtrack_reset();
    }

    if (bytes == 0) {
        void* p;
        uint64_t rnd = convert_from_cn_bits_u64(cn_gen_uniform_cn_bits_u64(0));
        if ((rnd % 2) == 0) {
            p = NULL;
        }
        else {
            p = alloc(1);
            uint64_t* size = alloc(sizeof(uint64_t));
            *size = bytes + 1;
            ht_set(pointer_size_map, (intptr_t*)&p, size);
        }
        return convert_to_cn_pointer(p);
    }
    else {
        void* p = alloc(bytes);
        uint64_t* size = alloc(sizeof(uint64_t));
        *size = bytes;
        ht_set(pointer_size_map, (intptr_t*)&p, size);
        return convert_to_cn_pointer(p);
    }
}

cn_pointer* cn_gen_aligned_alloc(cn_bits_u64* alignment, cn_bits_u64* sz) {
    uint64_t bytes = convert_from_cn_bits_u64(sz);
    if (cn_gen_backtrack_type() == CN_GEN_BACKTRACK_ALLOC) {
        bytes = cn_gen_backtrack_alloc_get();
        cn_gen_backtrack_reset();
    }

    uint64_t align = convert_from_cn_bits_u64(alignment);
    if (bytes != 0) {
        bytes = (bytes + (align - 1)) / align;
    }

    if (bytes == 0) {
        void* p;
        uint64_t rnd = convert_from_cn_bits_u64(cn_gen_uniform_cn_bits_u64(0));
        if ((rnd % 2) == 0) {
            p = NULL;
        }
        else {
            p = aligned_alloc(align, 1);
            uint64_t* size = alloc(sizeof(uint64_t));
            *size = bytes + 1;
            ht_set(pointer_size_map, (intptr_t*)&p, size);
        }
        return convert_to_cn_pointer(p);
    }
    else {
        void* p = aligned_alloc(align, bytes);
        uint64_t* size = alloc(sizeof(uint64_t));
        *size = bytes;
        ht_set(pointer_size_map, (intptr_t*)&p, size);
        return convert_to_cn_pointer(p);
    }
}

cn_bits_u64* cn_gen_alloc_size(cn_pointer* p) {
    void* ptr = convert_from_cn_pointer(p);
    if (ptr == NULL) {
        return convert_to_cn_bits_u64(0);
    }

    uint64_t* value = (uint64_t*)ht_get(pointer_size_map, (signed long*)&ptr);
    if (value == NULL) {
        return convert_to_cn_bits_u64(0);
    }

    return convert_to_cn_bits_u64(*value);
}
