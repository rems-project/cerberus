#include "cerberus.h"
long x = -1L;

int 
main (void)
{
  long b = (x != -1L);

  if (b)
    abort();

  exit(0);
}

