#include "cerberus.h"

int a = -1; 

int 
main (void)
{
  int b = a == 0 ? 0 : -a;
  if (b < 1)
    abort ();
  return 0;
}
