#include <stdint.h>

static inline void *copy_alloc_id(uintptr_t to, void *from) {
  return __cerbvar_copy_alloc_id(to, from);
}
