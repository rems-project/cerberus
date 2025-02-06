#ifndef CN_ALLOC
#define CN_ALLOC

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

    ////////////////////
    // Bump Allocator //
    ////////////////////

    void* cn_bump_aligned_alloc(size_t alignment, size_t nbytes);

    void* cn_bump_malloc(size_t nbytes);

    void* cn_bump_calloc(size_t count, size_t size);

    void cn_bump_free_all();

    typedef uintptr_t cn_bump_frame_id;

    cn_bump_frame_id cn_bump_get_frame_id(void);

    void cn_bump_free_after(cn_bump_frame_id frame_id);

    void cn_bump_print();

    //////////////////////////////////
    // Implicit Free List Allocator //
    //////////////////////////////////

    void* cn_fl_aligned_alloc(size_t alignment, size_t size);

    void* cn_fl_malloc(size_t size);

    void* cn_fl_calloc(size_t count, size_t size);

    void* cn_fl_realloc(void* p, size_t size);

    void cn_fl_free(void* p);

    void cn_fl_free_all();

    void cn_fl_print();

#ifdef __cplusplus
}
#endif

#endif // CN_ALLOC
