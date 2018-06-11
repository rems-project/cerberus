#include "cerberus.h"
/* The bit-field below would have a problem if __INT_MAX__ is too
   small.  */
#if __INT_MAX__ < 2147483647
int
main (void)
{
  exit (0);
}
#else
struct foo
{
  unsigned y:1;
  unsigned x:32;
};

int 
f (struct foo x)
{
  int t = x.x;
  if (t < 0)
    return 1;
  return t+1;
}

int 
main (void)
{
  struct foo x;
  x.x = -1;
  if (f (x) == 0)
    abort ();
  exit (0);
}
#endif
