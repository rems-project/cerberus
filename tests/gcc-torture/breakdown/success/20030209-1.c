#include "cerberus.h"
/* { dg-additional-options "-DSTACK_SIZE=[dg-effective-target-value stack_size]" { target { stack_size } } } */

#ifdef STACK_SIZE
#if STACK_SIZE < 8*100*100
#define SKIP
#endif
#endif

#ifndef SKIP
double x[100][100];
int 
main (void)
{
  int i;

  i = 99;
  x[i][0] = 42;
  if (x[99][0] != 42)
    abort ();
  exit (0);
}
#else
int 
main (void)
{
  exit (0);
}
#endif
