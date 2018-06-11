#include "cerberus.h"
/* { dg-require-effective-target int32plus } */
int 
foo (void)
{
  return 123;
}

int 
bar (void)
{
  int c = 1;
  c |= 4294967295 ^ (foo () | 4073709551608);
  return c;
}

int 
main (void)
{
  if (bar () != 0x83fd4005)
    __builtin_abort ();
}
