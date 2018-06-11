#include "cerberus.h"
/* PR rtl-optimization/78378 */

unsigned long long 
foo (unsigned long long x)
{
  x <<= 41;
  x /= 232;
  return 1 + (unsigned short) x;
}

int 
main (void)
{
  unsigned long long x = foo (1);
  if (x != 0x2c24)
    __builtin_abort();
  return 0;
}
