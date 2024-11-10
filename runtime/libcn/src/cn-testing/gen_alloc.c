#include "stdlib.h"

#include <cn-executable/utils.h>
#include <cn-testing/prelude.h>

#define MEM_SIZE (1024 * 1024 * 256)
static char alloc_buf[MEM_SIZE];
static void* alloc_curr = alloc_buf;

void cn_gen_alloc_reset(void) {
    alloc_curr = alloc_buf;
}

void* cn_gen_alloc_save(void) {
    return alloc_curr;
}

void cn_gen_alloc_restore(void* ptr) {
    alloc_curr = ptr;
}

static char ownership_buf[MEM_SIZE];
static void* ownership_curr = ownership_buf;

void cn_gen_ownership_reset(void) {
    ownership_curr = ownership_buf;
}

void* cn_gen_ownership_save(void) {
    return ownership_curr;
}

void cn_gen_ownership_restore(void* ptr) {
    ownership_curr = ptr;
}

struct pointer_data {
    void* ptr;
    size_t sz;
};

static void update_alloc(void* ptr, size_t sz) {
    if ((uintptr_t)alloc_curr - (uintptr_t)alloc_buf + sizeof(struct pointer_data) > MEM_SIZE) {
        printf("Out of space for allocation metadata!\n");
        exit(1);
    }
    *(struct pointer_data*)alloc_curr = (struct pointer_data){ .ptr = ptr, .sz = sz };
    alloc_curr = (char*)alloc_curr + sizeof(struct pointer_data);
}

static void update_ownership(void* ptr, size_t sz) {
    if ((uintptr_t)ownership_curr - (uintptr_t)ownership_buf + sizeof(struct pointer_data) > MEM_SIZE) {
        printf("Out of space for ownership metadata!\n");
        exit(1);
    }
    *(struct pointer_data*)ownership_curr = (struct pointer_data){ .ptr = ptr, .sz = sz };
    ownership_curr = (char*)ownership_curr + sizeof(struct pointer_data);
}

static uint8_t null_in_every = 4;

void set_null_in_every(uint8_t n) {
    null_in_every = n;
}

cn_pointer* cn_gen_alloc(cn_bits_u64* sz) {
    uint64_t bytes = convert_from_cn_bits_u64(sz);
    if (cn_gen_backtrack_type() == CN_GEN_BACKTRACK_ALLOC) {
        bytes = cn_gen_backtrack_alloc_get();
        cn_gen_backtrack_reset();
    }
    else if (bytes == 0) {
        uint64_t rnd = convert_from_cn_bits_u8(cn_gen_uniform_cn_bits_u8(null_in_every));
        if (rnd == 0) {
            bytes = 0;
        }
        else {
            bytes = 8;
        }
    }

    if (bytes == 0) {
        return convert_to_cn_pointer(NULL);
    }
    else {
        void* p = alloc(bytes);
        update_alloc(p, bytes);
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
        uint64_t rnd = convert_from_cn_bits_u8(cn_gen_uniform_cn_bits_u8(null_in_every));
        if (rnd == 0) {
            p = NULL;
        }
        else {
            p = aligned_alloc(align, 1);
            update_alloc(p, 1);
        }
        return convert_to_cn_pointer(p);
    }
    else {
        void* p = aligned_alloc(align, bytes);
        update_alloc(p, bytes);
        return convert_to_cn_pointer(p);
    }
}

int cn_gen_alloc_check(void* p, size_t sz) {
    if (alloc_curr == alloc_buf) {
        return 0;
    }

    int bytes = sz;

    struct pointer_data* q = (struct pointer_data*)(
        (uintptr_t)alloc_curr - sizeof(struct pointer_data));
    for (; (uintptr_t)q >= (uintptr_t)alloc_buf; q--) {
        uintptr_t lb = (uintptr_t)q->ptr;
        uintptr_t ub = (uintptr_t)q->ptr + q->sz;
        if (lb < (uintptr_t)p) {
            lb = (uintptr_t)p;
        }
        if (ub > (uintptr_t)p + sz) {
            ub = (uintptr_t)p + sz;
        }
        if (ub > lb) {
            bytes -= (ub - lb);
        }

        if (bytes == 0) {
            return 1;
        }
    }
    assert(bytes >= 0);
    return (bytes == 0);
}

void cn_gen_ownership_update(void* p, size_t sz) {
    update_ownership(p, sz);
}

int cn_gen_ownership_check(void* p, size_t sz) {
    if (ownership_curr == ownership_buf) {
        return 1;
    }

    int bytes = sz;

    struct pointer_data* q = (struct pointer_data*)(
        (uintptr_t)ownership_curr - sizeof(struct pointer_data));
    for (; (uintptr_t)q >= (uintptr_t)ownership_buf; q--) {
        uintptr_t lb = (uintptr_t)q->ptr;
        uintptr_t ub = (uintptr_t)q->ptr + q->sz;
        if (lb < (uintptr_t)p) {
            lb = (uintptr_t)p;
        }
        if (ub > (uintptr_t)p + sz) {
            ub = (uintptr_t)p + sz;
        }
        if (ub > lb) {
            return 0;
        }
    }

    return 1;
}
