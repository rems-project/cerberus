#include "cerberus.h"
int f(int k, int i1, int j1)
{
  int *f1;
  if(k)
   f1 = &i1;
  else
   f1 = &j1;
  i1 = 0;
  return *f1;
}


int 
main (void)
{
  if (f(1, 1, 2) != 0)
    abort ();
  return 0;
}
