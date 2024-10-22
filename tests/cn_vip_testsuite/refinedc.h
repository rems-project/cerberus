#include <stdint.h>

#if defined(__cerb__) && defined(VIP)
#define copy_alloc_id(to, from) __cerbvar_copy_alloc_id(to, from)
#else
#define copy_alloc_id(to, from) ((uintptr_t) (from), (void*) (to))
#endif
