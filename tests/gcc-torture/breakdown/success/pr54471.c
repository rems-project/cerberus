#include "cerberus.h"
/* PR tree-optimization/54471 */

#ifdef __SIZEOF_INT128__
#define T __int128
#else
#define T long long
#endif



unsigned T
foo (T ixi, unsigned ctr)
{
  unsigned T irslt = 1;
  T ix = ixi;

  for (; ctr; ctr--)
    {
      irslt *= ix;
      ix *= ix;
    }

  if (irslt != 14348907)
    abort ();
  return irslt;
}

int 
main (void)
{
  unsigned T res;

  res = foo (3, 4);
  return 0;
}
