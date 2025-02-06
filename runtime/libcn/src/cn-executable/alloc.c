#include <stdlib.h>
#include <stdalign.h>
#include <string.h>

#ifdef CN_DEBUG_PRINTING
#   include <stdio.h>
#endif

#include <cn-executable/alloc.h>
#include <cn-executable/utils.h>


////////////////////
// Bump Allocator //
////////////////////

#define BUMP_MEM_SIZE (1024 * 1024 * 512)
char bump_mem[BUMP_MEM_SIZE];
static char* bump_curr = bump_mem;


#ifdef CN_DEBUG_PRINTING
void cn_bump_fprint(FILE* file) {
    fprintf(file, "Start: %p, Next: %p\n", bump_mem, bump_curr);
}

void cn_bump_print() {
    cn_bump_fprint(stdout);
}
#else
void cn_bump_fprint(FILE* file) {}

void cn_bump_print() {}
#endif

void* cn_bump_aligned_alloc(size_t alignment, size_t nbytes) {
    if (nbytes == 0) {
        return NULL;
    }

    uintptr_t max = (uintptr_t)bump_mem + BUMP_MEM_SIZE;

    if ((uintptr_t)bump_curr % alignment != 0) {
        size_t padding = (alignment - (uintptr_t)bump_curr % alignment) % alignment;
        if ((uintptr_t)bump_curr + padding >= max) {
            cn_failure(CN_FAILURE_ALLOC);
            return NULL;
        }
        bump_curr += padding;
    }

    void* res = bump_curr;
    if ((uintptr_t)bump_curr + nbytes >= max) {
        cn_failure(CN_FAILURE_ALLOC);
        return NULL;
    }
    bump_curr += nbytes;

    return res;
}

void* cn_bump_malloc(size_t nbytes) {
    return cn_bump_aligned_alloc(alignof(max_align_t), nbytes);
}

void* cn_bump_calloc(size_t count, size_t size) {
    size_t nbytes = count * size;

    void* p = cn_bump_malloc(nbytes);
    if (p != NULL) {
        memset(p, 0, nbytes);
    }
    return p;
}

void cn_bump_free_all(void) {
    bump_curr = bump_mem;
}

cn_bump_frame_id cn_bump_get_frame_id(void) {
    return (uintptr_t)bump_curr;
}

void cn_bump_free_after(cn_bump_frame_id frame_id) {
    bump_curr = (char*)frame_id;
}


//////////////////////////////////
// Implicit Free List Allocator //
//////////////////////////////////

typedef struct free_list_node {
    uint32_t size;
} free_list_node;

// Has to fit in `uint32_t`
#define FL_MEM_SIZE (1024 * 1024 * 512)
char free_list_mem[FL_MEM_SIZE];
static free_list_node* free_list;
static free_list_node* first_free;

static inline int fl_is_used(free_list_node* fl) {
    return fl->size & 1;
}

static inline uint32_t fl_size(free_list_node* fl) {
    return fl->size & ~((uint32_t)1);
}

static inline free_list_node* fl_tag(void* p) {
    return (free_list_node*)((uintptr_t)p - sizeof(free_list_node));
}

static inline free_list_node* fl_boundary_tag(free_list_node* fl) {
    return (free_list_node*)((uintptr_t)fl + sizeof(free_list_node) + fl_size(fl));
}

static inline void fl_set_size(free_list_node* fl, size_t size) {
    char used = fl_is_used(fl);
    fl->size = size | used;
    fl_boundary_tag(fl)->size = fl->size;
}

static inline void fl_set_taken(free_list_node* fl) {
    fl->size |= 1;
    fl_boundary_tag(fl)->size |= 1;
}

static inline void fl_set_free(free_list_node* fl) {
    fl->size &= ~((uint32_t)1);
    fl_boundary_tag(fl)->size &= ~((uint32_t)1);
}

static inline free_list_node* fl_next_node(free_list_node* fl) {
    uintptr_t possible_next = (uintptr_t)fl + fl_size(fl) + 2 * sizeof(free_list_node);
    uintptr_t max = (uintptr_t)free_list_mem + FL_MEM_SIZE - 2 * sizeof(free_list_node);
    if (possible_next >= max) {
        return NULL;
    }

    return (free_list_node*)possible_next;
}

static inline free_list_node* fl_prev_node(free_list_node* fl) {
    free_list_node* possible_boundary_tag = (free_list_node*)((uintptr_t)fl - sizeof(free_list_node));
    uintptr_t possible_prev = (uintptr_t)possible_boundary_tag - fl_size(possible_boundary_tag) - sizeof(free_list_node);
    uintptr_t min = (uintptr_t)free_list;
    if (possible_prev < min) {
        return NULL;
    }

    return (free_list_node*)possible_prev;
}

#ifdef CN_DEBUG_PRINTING
void cn_fl_fprint(FILE* file) {
    free_list_node* curr = free_list;

    while (curr) {
        if (fl_is_used(curr)) {
            fprintf(file, "Block %d (x) | %d, ", fl_size(curr), fl_boundary_tag(curr)->size);
        }
        else {
            fprintf(file, "Block %d ( ) | %d, ", fl_size(curr), fl_boundary_tag(curr)->size);
        }

        curr = fl_next_node(curr);
    }
    printf("\n");
}

void cn_fl_print() {
    cn_fl_fprint(stdout);
}
#else
void cn_fl_fprint(FILE* file) {}

void cn_fl_print() {}
#endif

void cn_fl_free_all() {
    size_t padding =
        (alignof(max_align_t) - ((uintptr_t)free_list_mem + sizeof(free_list_node))
            % alignof(max_align_t))
        % alignof(max_align_t);
    if (!free_list) {
        free_list = (free_list_node*)((uintptr_t)free_list_mem + padding);
    }
    first_free = free_list;
    fl_set_free(free_list);
    fl_set_size(free_list, FL_MEM_SIZE - padding - 2 * sizeof(free_list_node));
}

void cn_fl_init(void) {
    if (!free_list) {
        cn_fl_free_all();
    }
}

static inline void fl_coalesce(free_list_node* fl) {
    if (fl == NULL || fl_is_used(fl)) {
        return;
    }

    free_list_node* prev = fl_prev_node(fl);
    free_list_node* next = fl_next_node(fl);

    int prev_used = prev == NULL || fl_is_used(prev);
    int next_used = next == NULL || fl_is_used(next);

    if (!prev_used && !next_used)
    {
        fl_set_size(prev, fl_size(prev) + fl_size(fl) + fl_size(next) + 4 * sizeof(free_list_node));
    }
    else if (prev_used && !next_used)
    {
        fl_set_size(fl, fl_size(fl) + fl_size(next) + 2 * sizeof(free_list_node));
    }
    else if (!prev_used && next_used)
    {
        fl_set_size(prev, fl_size(prev) + fl_size(fl) + 2 * sizeof(free_list_node));
    }
}

static inline size_t gcd(size_t a, size_t b) {
    while (b != 0) {
        size_t temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

static inline size_t lcm(size_t a, size_t b) {
    return (a * b) / gcd(a, b);
}

void* cn_fl_aligned_alloc(size_t alignment, size_t size) {
    if (size == 0) {
        return NULL;
    }

    cn_fl_init();

    if (alignment % alignof(free_list_node) != 0) {
        alignment = lcm(alignment, alignof(free_list_node));
    }

    free_list_node* curr = first_free;

    while (curr && fl_is_used(curr)) {
        curr = fl_next_node(curr);
        first_free = curr;
    }

    while (curr) {
        if (fl_is_used(curr)) {
            curr = fl_next_node(curr);
            continue;
        }

        free_list_node* prev = fl_prev_node(curr);

        int was_first_free = curr == first_free;

        // Calculate padding
        uintptr_t curr_addr = (uintptr_t)curr;

        size_t back_padding =
            (alignof(free_list_node) - (size)
                % alignof(free_list_node))
            % alignof(free_list_node);

        size_t padding = (alignment - (curr_addr + sizeof(free_list_node)) % alignment) % alignment;
        if (padding != 0) {
            free_list_node* next = fl_next_node(curr);
            size_t memory_left = fl_size(curr) - (padding + size + back_padding);
            size_t memory_left_aligned = (memory_left / alignment) * alignment;
            if (next == NULL
                || (fl_is_used(next)
                    && !fl_is_used(prev)
                    && memory_left - memory_left_aligned >= 2 * sizeof(free_list_node))) {
                padding += memory_left_aligned;
            }
        }

        uintptr_t aligned_addr = curr_addr + padding;

        if (fl_size(curr) >= padding + size + back_padding) {
            fl_set_taken(curr);

            if (padding != 0) {
                if ((prev == NULL || fl_is_used(prev)) && padding >= 2 * sizeof(free_list_node)) {
                    size_t orig_size = fl_size(curr);

                    // Split padding into new block
                    /// Make new block
                    fl_set_size(curr, padding - 2 * sizeof(free_list_node));
                    fl_set_free(curr);
                    prev = curr;

                    /// Shift current block
                    curr = (free_list_node*)aligned_addr;
                    fl_set_size(curr, orig_size - padding);
                    fl_set_taken(curr);

                    // `curr` (now `prev`) is still free
                    if (was_first_free) {
                        was_first_free = 0;
                    }
                }
                else
                {
                    if (prev != NULL) {
                        // Coalesce padding with previous block
                        fl_set_size(prev, fl_size(prev) + padding);
                    }

                    /// Shift current block
                    curr = (free_list_node*)aligned_addr;
                    fl_set_size(curr, size - padding);
                    fl_set_taken(curr);
                }
            }

            if (fl_size(curr) > size + back_padding) {
                size_t memory_left = fl_size(curr) - (size + back_padding);
                if (memory_left >= 2 * sizeof(free_list_node)) {
                    fl_set_size(curr, size + back_padding);

                    free_list_node* next = fl_next_node(curr);
                    fl_set_size(next, memory_left - 2 * sizeof(free_list_node));
                    fl_set_free(next);

                    fl_coalesce(next);
                }
            }

            if (was_first_free) {
                first_free = fl_next_node(curr);
            }

            return (void*)(aligned_addr + sizeof(free_list_node));
        }

        curr = fl_next_node(curr);
    }

    cn_failure(CN_FAILURE_ALLOC); // Out of memory
    return NULL;
}

void* cn_fl_malloc(size_t size) {
    return cn_fl_aligned_alloc(alignof(max_align_t), size);
}

void* cn_fl_calloc(size_t count, size_t size) {
    size_t nbytes = count * size;

    void* p = cn_fl_malloc(nbytes);
    if (p != NULL) {
        memset(p, 0, nbytes);
    }
    return p;
}

void* cn_fl_realloc(void* p, size_t nbytes) {
    if (p == NULL) {
        return cn_fl_malloc(nbytes);
    }

    free_list_node* fl = fl_tag(p);

    if (fl_size(fl) >= nbytes) {
        return p;
    }

    // Steal some memory from the next block
    free_list_node* next = fl_next_node(fl);
    if (next != NULL && !fl_is_used(next)) {
        size_t back_padding =
            (alignof(free_list_node) - nbytes
                % alignof(free_list_node))
            % alignof(free_list_node);

        size_t memory_available = fl_size(fl) + fl_size(next) + 2 * sizeof(free_list_node);
        if (memory_available > nbytes + back_padding) {
            size_t memory_left = memory_available - (nbytes + back_padding);
            if (memory_left >= 2 * sizeof(free_list_node)) {
                fl_set_size(fl, nbytes + back_padding);

                free_list_node* next = fl_next_node(fl);
                fl_set_size(next, memory_left - 2 * sizeof(free_list_node));
                fl_set_free(next);

                return p;
            }
            else {
                fl_set_size(fl, memory_available);
                return p;
            }
        }
    }

    // Could steal memory from previous block?
    // Fuse the free + malloc?

    void* res = cn_fl_malloc(nbytes);
    size_t copy_size = (nbytes < fl_size(fl)) ? nbytes : fl_size(fl);
    memcpy(res, p, copy_size);
    cn_fl_free(p);
    return res;
}

void cn_fl_free(void* p) {
    free_list_node* tag = fl_tag(p);
    fl_set_free(tag);

    if (!first_free || tag < first_free) {
        first_free = tag;
    }

    fl_coalesce(tag);
}
