#include "cerberus.h"
int 
ts (int a)
{
  if (a < 1000 && a > 2000)
    return 1;
  else
    return 0;
}

int 
tu (unsigned int a)
{
  if (a < 1000 && a > 2000)
    return 1;
  else
    return 0;
}


int 
main (void)
{
  if (ts (0) || tu (0))
    abort ();
  exit (0);
}
