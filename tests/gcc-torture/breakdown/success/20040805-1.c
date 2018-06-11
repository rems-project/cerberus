#include "cerberus.h"
/* { dg-additional-options "-DSTACK_SIZE=[dg-effective-target-value stack_size]" { target { stack_size } } } */

#if __INT_MAX__ < 32768 || (defined(STACK_SIZE) && STACK_SIZE < 0x12000)
int 
main (void) { exit (0); }
#else
int a[2] = { 2, 3 };

static int 
bar (int x, void *b)
{
  a[0]++;
  return x;
}

static int 
foo (int x)
{
  char buf[0x10000];
  int y = a[0];
  a[1] = y;
  x = bar (x, buf);
  y = bar (y, buf);
  return x + y;
}

int 
main (void)
{
  if (foo (100) != 102)
    abort ();
  exit (0);
}
#endif
