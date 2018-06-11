#include "cerberus.h"
/* { dg-require-effective-target trampolines } */

int 
main (void)
{
  int i = 0;
  int a (int x)
    {
      while (x)
	i++, x--;
      return x;
    }

  if (a (2) != 0)
    abort ();

  exit (0);
}
