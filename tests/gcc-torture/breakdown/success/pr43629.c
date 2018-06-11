#include "cerberus.h"
int flag;
int 
main (void)
{
  int x;
  if (flag)
    x = -1;
  else 
    x &= 0xff;
  if (x & ~0xff)
    abort ();
  return 0;
}
