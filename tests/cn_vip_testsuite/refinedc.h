#include <stdint.h>

static inline void *copy_alloc_id(uintptr_t to, void *from)
/*@ ensures (alloc_id) return == (alloc_id) from;
            (u64) return == (u64) to; @*/
{
#if defined(__cerb__) && defined(VIP)
    return __cerbvar_copy_alloc_id(to, from);
#else
  return ((uintptr_t) (from), (void*) (to));
#endif
}
