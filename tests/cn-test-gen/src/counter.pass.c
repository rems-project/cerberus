#include <stdint.h>

static uint64_t __count = 0;

uint64_t count()
/*@ accesses __count;
    requires
        __count < 100u64;
  @*/
{
    return __count++;
}
