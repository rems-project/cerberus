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
// Explicit Free List Allocator //
//////////////////////////////////

typedef struct block_header {
    uint32_t size;
} block_header;

typedef struct free_block_header {
    block_header header;
    uint32_t next;
    uint32_t prev;
} free_block_header;


// Has to fit in `uint32_t`
#define FL_MEM_SIZE (1024 * 1024 * 512)
char free_list_mem[FL_MEM_SIZE];
static block_header* block_list;
static free_block_header* first_free;

#define BLOCK_LIST_PADDING \
    ((alignof(max_align_t) - ((uintptr_t)free_list_mem + sizeof(block_header))\
            % alignof(max_align_t))\
        % alignof(max_align_t))
#define MIN_BLOCK_SIZE (sizeof(free_block_header) + sizeof(block_header))
#define MAX_BLOCK_INDEX (FL_MEM_SIZE - MIN_BLOCK_SIZE - BLOCK_LIST_PADDING)
#define NULL_BLOCK_INDEX (MAX_BLOCK_INDEX + 1)

static inline int fl_is_used(block_header* fl) {
    return fl->size & 1;
}

static inline uint32_t fl_size(block_header* fl) {
    return fl->size & ~((uint32_t)1);
}

static inline block_header* fl_tag(void* p) {
    return (block_header*)((uintptr_t)p - sizeof(block_header));
}

static inline block_header* fl_boundary_tag(block_header* fl) {
    return (block_header*)((uintptr_t)fl + sizeof(block_header) + fl_size(fl));
}

static inline int fl_is_valid_tag(block_header* fl) {
    return (free_list_mem < (char*)fl)
        && ((char*)fl <= free_list_mem + MAX_BLOCK_INDEX)
        && (fl->size == fl_boundary_tag(fl)->size);
}

static inline void fl_set_size(block_header* fl, size_t size) {
    char used = fl_is_used(fl);
    fl->size = size | used;
    fl_boundary_tag(fl)->size = fl->size;
}

static inline void fl_set_taken(block_header* fl) {
    fl->size |= 1;
    fl_boundary_tag(fl)->size = fl->size;
}

static inline void fl_set_free(block_header* fl) {
    fl->size &= ~((uint32_t)1);
    fl_boundary_tag(fl)->size = fl->size;
}

static inline block_header* fl_next_node(block_header* fl) {
    uintptr_t possible_next = (uintptr_t)fl + fl_size(fl) + 2 * sizeof(block_header);
    uintptr_t max = (uintptr_t)free_list_mem + FL_MEM_SIZE - MIN_BLOCK_SIZE;
    if (possible_next >= max) {
        return NULL;
    }

    return (block_header*)possible_next;
}

static inline block_header* fl_prev_node(block_header* fl) {
    block_header* possible_boundary_tag = (block_header*)((uintptr_t)fl - sizeof(block_header));
    uintptr_t possible_prev = (uintptr_t)possible_boundary_tag - fl_size(possible_boundary_tag) - sizeof(block_header);
    uintptr_t min = (uintptr_t)block_list;
    if (possible_prev < min) {
        return NULL;
    }

    return (block_header*)possible_prev;
}

static inline uint32_t fl_offset(block_header* fl) {
    return (uintptr_t)fl - (uintptr_t)block_list;
}

static inline free_block_header* fl_by_offset(uint32_t offset) {
    return (free_block_header*)((uintptr_t)block_list + offset);
}

static inline free_block_header* fl_next_free_node(free_block_header* fl) {
    if (fl->next > MAX_BLOCK_INDEX) {
        return NULL;
    }

    return (free_block_header*)((uintptr_t)block_list + fl->next);
}

static inline free_block_header* fl_prev_free_node(free_block_header* fl) {
    if (fl->prev > MAX_BLOCK_INDEX) {
        return NULL;
    }

    return (free_block_header*)((uintptr_t)block_list + fl->prev);
}

#ifdef CN_DEBUG_PRINTING
void cn_fl_fprint(FILE* file) {
    block_header* curr = block_list;

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
    if (!block_list) {
        block_list = (block_header*)((uintptr_t)free_list_mem + BLOCK_LIST_PADDING);
    }
    first_free = (free_block_header*)block_list;
    first_free->prev = NULL_BLOCK_INDEX;
    first_free->next = NULL_BLOCK_INDEX;
    fl_set_size(block_list, FL_MEM_SIZE - BLOCK_LIST_PADDING - 2 * sizeof(block_header));
    fl_set_free(block_list);
}

void cn_fl_init(void) {
    if (!block_list) {
        cn_fl_free_all();
    }
}

// Takes a free block's header, where the `next` and `prev` pointers are valid
static inline void fl_coalesce(free_block_header* fl) {
    if (fl == NULL || fl_is_used(&fl->header)) {
        return;
    }

    block_header* prev = fl_prev_node(&fl->header);
    block_header* next = fl_next_node(&fl->header);

    int prev_used = prev == NULL || fl_is_used(prev);
    int next_used = next == NULL || fl_is_used(next);

    free_block_header* prev_free = fl_prev_free_node(fl);

    free_block_header* prev_free_prev = NULL;
    if (prev_free) {
        prev_free_prev = fl_prev_free_node((free_block_header*)prev);
    }

    free_block_header* next_free = fl_next_free_node(fl);

    free_block_header* next_free_next = NULL;
    if (next_free) {
        next_free_next = fl_next_free_node((free_block_header*)next);
    }

    if (!prev_used && !next_used)
    {
        if (prev_free_prev) {
            prev_free->prev = fl_offset(&prev_free_prev->header);
            prev_free_prev->next = fl_offset(&prev_free->header);
        }
        else {
            first_free = prev_free;
            prev_free->prev = NULL_BLOCK_INDEX;
        }

        if (next_free_next) {
            prev_free->next = fl_offset(&next_free_next->header);
            next_free_next->prev = fl_offset(&prev_free->header);
        }
        else {
            prev_free->next = NULL_BLOCK_INDEX;
        }

        fl_set_size(prev, fl_size(prev) + fl_size(&fl->header) + fl_size(next) + 4 * sizeof(block_header));
    }
    else if (prev_used && !next_used)
    {
        if (prev_free) {
            fl->prev = fl_offset(&prev_free->header);
            prev_free->next = fl_offset(&fl->header);
        }
        else {
            first_free = fl;
            fl->prev = NULL_BLOCK_INDEX;
        }

        if (next_free_next) {
            fl->next = fl_offset(&next_free_next->header);
            next_free_next->prev = fl_offset(&fl->header);
        }
        else {
            fl->next = NULL_BLOCK_INDEX;
        }

        fl_set_size(&fl->header, fl_size(&fl->header) + fl_size(next) + 2 * sizeof(block_header));
    }
    else if (!prev_used && next_used)
    {
        if (prev_free_prev) {
            prev_free->prev = fl_offset(&prev_free_prev->header);
            prev_free_prev->next = fl_offset(&prev_free->header);
        }
        else {
            first_free = prev_free;
            prev_free->prev = NULL_BLOCK_INDEX;
        }

        if (next_free) {
            prev_free->next = fl_offset(&next_free->header);
            next_free->prev = fl_offset(&prev_free->header);
        }
        else {
            prev_free->next = NULL_BLOCK_INDEX;
        }

        fl_set_size(prev, fl_size(prev) + fl_size(&fl->header) + 2 * sizeof(block_header));
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

    if (alignment % alignof(free_block_header) != 0) {
        alignment = lcm(alignment, alignof(free_block_header));
    }

    if (size < MIN_BLOCK_SIZE) {
        size = MIN_BLOCK_SIZE;
    }

    free_block_header* curr = first_free;
    int was_first_free = 1;

    while (curr) {
        block_header* prev = fl_prev_node(&curr->header);

        uintptr_t curr_addr = (uintptr_t)curr;

        size_t back_padding =
            (alignof(block_header) - size
                % alignof(block_header))
            % alignof(block_header);

        size_t padding = (alignment - (curr_addr + sizeof(block_header)) % alignment) % alignment;
        if (padding != 0) {
            block_header* next = fl_next_node(&curr->header);
            size_t memory_left = fl_size(&curr->header) - (padding + size + back_padding);
            size_t memory_left_aligned = (memory_left / alignment) * alignment;
            if (next == NULL
                || (fl_is_used(next)
                    && !fl_is_used(prev)
                    && memory_left - memory_left_aligned >= 2 * sizeof(block_header))) {
                padding += memory_left_aligned;
            }
        }

        uintptr_t aligned_addr = curr_addr + padding;

        // If allocation fits
        if (fl_size(&curr->header) >= padding + size + back_padding) {
            fl_set_taken(&curr->header);
            if (was_first_free) {
                first_free = NULL;
            }

            free_block_header* prev_free = fl_prev_free_node(curr);
            free_block_header* next_free = fl_next_free_node(curr);

            // Skip current block in free list
            if (prev_free) {
                prev_free->next = fl_offset(&next_free->header);
            }
            if (next_free) {
                next_free->prev = fl_offset(&prev_free->header);

                if (was_first_free) {
                    first_free = next_free;
                }
            }

            if (padding != 0) {
                size_t orig_size = fl_size(&curr->header);

                // Split padding into new block
                if ((prev == NULL || fl_is_used(prev)) && padding >= MIN_BLOCK_SIZE) {
                    // Make new block
                    fl_set_size(&curr->header, padding - 2 * sizeof(block_header));
                    fl_set_free(&curr->header);
                    prev = &curr->header;

                    // Reinsert `curr` into free list
                    if (prev_free) {
                        prev_free->next = fl_offset(&curr->header);
                    }
                    if (next_free) {
                        next_free->prev = fl_offset(&curr->header);
                    }

                    if (was_first_free) {
                        first_free = curr;
                        was_first_free = 0;
                    }
                }
                else if (prev != NULL) {
                    // Coalesce padding with previous block
                    fl_set_size(prev, fl_size(prev) + padding);
                }

                // Shift current block
                curr = (free_block_header*)aligned_addr;
                fl_set_size(&curr->header, orig_size - padding);
                fl_set_taken(&curr->header);
            }

            size_t memory_left = fl_size(&curr->header) - (size + back_padding);

            if (memory_left >= MIN_BLOCK_SIZE) {
                fl_set_size(&curr->header, size + back_padding);

                free_block_header* next = (free_block_header*)fl_next_node(&curr->header);
                fl_set_size(&next->header, memory_left - 2 * sizeof(block_header));
                fl_set_free(&next->header);

                if (prev_free) {
                    prev_free->next = fl_offset(&next->header);
                    next->prev = fl_offset(&prev_free->header);
                }
                else {
                    next->prev = NULL_BLOCK_INDEX;
                }

                if (next_free) {
                    next->next = fl_offset(&next_free->header);
                    next_free->prev = fl_offset(&next->header);
                }
                else {
                    next->next = NULL_BLOCK_INDEX;
                }

                if (was_first_free) {
                    first_free = next;
                }
            }

            return (void*)(aligned_addr + sizeof(block_header));
        }

        curr = fl_next_free_node(curr);
        was_first_free = 0;
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

    block_header* fl = fl_tag(p);

    if (fl_size(fl) >= nbytes) {
        return p;
    }

    // Steal some memory from the next block
    block_header* next = fl_next_node(fl);
    if (next != NULL && !fl_is_used(next)) {
        size_t back_padding =
            (alignof(free_block_header) - nbytes
                % alignof(free_block_header))
            % alignof(free_block_header);

        size_t memory_available = fl_size(fl) + fl_size(next) + 2 * sizeof(block_header);
        if (memory_available > nbytes + back_padding) {
            size_t memory_left = memory_available - (nbytes + back_padding);
            if (memory_left >= MIN_BLOCK_SIZE) {
                free_block_header* prev_free = fl_prev_free_node((free_block_header*)next);
                free_block_header* next_free = fl_prev_free_node((free_block_header*)next);

                fl_set_size(fl, nbytes + back_padding);

                block_header* new_next = fl_next_node(fl);
                fl_set_size(new_next, memory_left - 2 * sizeof(block_header));
                fl_set_free(new_next);

                prev_free->next = fl_offset(new_next);
                next_free->prev = fl_offset(new_next);

                return p;
            }
            else {
                fl_set_size(fl, memory_available);
                return p;
            }
        }
    }

    void* res = cn_fl_malloc(nbytes);
    size_t copy_size = (nbytes < fl_size(fl)) ? nbytes : fl_size(fl);
    memcpy(res, p, copy_size);
    cn_fl_free(p);
    return res;
}

void cn_fl_free(void* p) {
    if (p == NULL) {
        return;
    }

    free_block_header* tag = (free_block_header*)fl_tag(p);

    if (!fl_is_valid_tag(&tag->header)) {
        fprintf(stderr, "Tried to free an invalid block");
        exit(1);
    }

    if (!fl_is_used(&tag->header)) {
        fprintf(stderr, "Tried to free already free block");
        exit(1);
    }

    fl_set_free(&tag->header);

    if (!first_free) {
        first_free = tag;

        tag->prev = NULL_BLOCK_INDEX;
        tag->next = NULL_BLOCK_INDEX;

        return;
    }

    struct free_block_header* prev = NULL;
    struct free_block_header* curr = first_free;
    while (curr) {
        if (tag < curr) {
            if (prev) {
                tag->prev = fl_offset(&prev->header);
                prev->next = fl_offset(&tag->header);
            }
            else {
                first_free = tag;
                tag->prev = NULL_BLOCK_INDEX;
            }

            tag->next = fl_offset(&curr->header);
            curr->prev = fl_offset(&tag->header);

            fl_coalesce(tag);

            return;
        }

        prev = curr;
        curr = fl_next_free_node(curr);
    }

    prev->next = fl_offset(&tag->header);
    tag->prev = fl_offset(&prev->header);
    tag->next = NULL_BLOCK_INDEX;

    fl_coalesce(tag);
}
