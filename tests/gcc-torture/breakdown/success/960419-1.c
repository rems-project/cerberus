#include "cerberus.h"
static int i;

void 
check (int x)
{
  if (!x)
    abort();
}

int 
main (void)
{
  int *p = &i;

  check(p != (void *)0);
  exit (0);
}
