#include "cerberus.h"
static int a[199];

static void 
foo (void)
{
  int i;
  for (i = 198; i >= 0; i--)
    a[i] = i;
}

int 
main (void)
{
  int i;
  foo ();
  for (i = 0; i < 199; i++)
    if (a[i] != i)
      abort ();
  return 0;
}
