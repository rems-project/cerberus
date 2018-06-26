#include "cerberus.h"
/* PR tree-optimization/19283 */

static inline unsigned short
foo (unsigned int *p)
{
  return *p;
}

unsigned int u;

int 
main (void)
{
  if ((foo (&u) & 0x8000) != 0)
    abort ();
  return 0;
}
