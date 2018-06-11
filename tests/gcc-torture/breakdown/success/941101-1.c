#include "cerberus.h"
int 
f (void)
{
  int var = 7;

  if ((var/7) == 1)
    return var/7;
  return 0;
}

int 
main (void)
{
  if (f () != 1)
    abort ();
  exit (0);
}
