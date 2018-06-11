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
int 
main (void)
{
  struct
    {
      signed int bf0:17;
      signed int bf1:7;
    } bf;

  bf.bf1 = 7;
  f (bf.bf1);
  exit (0);
}

int 
f (int x)
{
  if (x != 7)
    abort ();
}
#endif
