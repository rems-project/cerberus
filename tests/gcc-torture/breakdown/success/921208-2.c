#include "cerberus.h"
/* { dg-require-effective-target untyped_assembly } */
/* { dg-additional-options "-DSTACK_SIZE=[dg-effective-target-value stack_size]" { target { stack_size } } } */

#define STACK_REQUIREMENT (100000 * 4 + 1024)
#if defined (STACK_SIZE) && STACK_SIZE < STACK_REQUIREMENT
int 
main (void) { exit (0); }
#else

int 
g (void){}

int 
f (void)
{
  int i;
  float a[100000];

  for (i = 0; i < 1; i++)
    {
      g(1.0, 1.0 + i / 2.0 * 3.0);
      g(2.0, 1.0 + i / 2.0 * 3.0);
    }
}

int 
main (void)
{
  f();
  exit(0);
}

#endif
