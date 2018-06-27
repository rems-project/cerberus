#include "cerberus.h"
int
f (int b, int c)
{
  if (b != 0 && b != 1 && c != 0)
    b = 0;
  return b;
}

int 
main (void)
{
  if (!f (1, 2))
    abort();
  exit(0);
}
