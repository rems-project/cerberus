#include "cerberus.h"
/* { dg-options "-std=c99" } */

long long a = -1;
long long llabs (long long);
int 
main (void)
{
  if (llabs (a) != 1)
    abort ();
  return 0;
}
long long llabs (long long b)
{
	abort ();
}
