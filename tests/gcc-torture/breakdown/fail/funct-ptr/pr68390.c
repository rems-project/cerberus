#include "cerberus.h"
/* { dg-do run }  */
/* { dg-options "-O2" } */


double direct(int x, ...)
{
  return x*x;
}


double broken(double (*indirect)(int x, ...), int v)
{
  return indirect(v);
}

int 
main (void)
{
  double d1, d2;
  int i = 2;
  d1 = broken (direct, i);
  if (d1 != i*i)
    {
      __builtin_abort ();
    }
  return 0;
}

