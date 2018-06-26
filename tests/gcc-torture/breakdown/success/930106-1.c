#include "cerberus.h"
/* { dg-additional-options "-DSTACK_SIZE=[dg-effective-target-value stack_size]" { target { stack_size } } } */

#if defined (STACK_SIZE)
#define DUMMY_SIZE 9
#else
#define DUMMY_SIZE 399999
#endif

double 
g (void)
{
  return 1.0;
}

int 
f (void)
{
  char dummy[DUMMY_SIZE];
  double f1, f2, f3;
  f1 = g();
  f2 = g();
  f3 = g();
  return f1 + f2 + f3;
}

int 
main (void)
{
  if (f() != 3.0)
    abort();
  exit(0);
}
