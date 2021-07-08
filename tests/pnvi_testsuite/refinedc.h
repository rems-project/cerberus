#include <stdint.h>

static inline void *copy_alloc_id(uintptr_t to, void *from) {
#if defined(__cerb__) && defined(VIP)
    return __cerbvar_copy_alloc_id(to, from);
#else
  return ((uintptr_t) (from), (void*) (to));
#endif
}
