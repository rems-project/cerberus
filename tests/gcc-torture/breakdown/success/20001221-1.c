#include "cerberus.h"
int 
main (void)
{
  unsigned long long a;
  if (! (a = 0xfedcba9876543210ULL))
    abort ();
  exit (0);
}
