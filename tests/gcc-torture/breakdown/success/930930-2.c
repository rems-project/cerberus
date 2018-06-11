#include "cerberus.h"
int 
test_endianness (void)
{
  union doubleword
    {
      double d;
      unsigned long u[2];
    } dw;
  dw.d = 10;
  return dw.u[0] != 0 ? 1 : 0;
}

int 
test_endianness_vol (void)
{
  union doubleword
    {
      volatile double d;
      volatile long u[2];
    } dw;
  dw.d = 10;
  return dw.u[0] != 0 ? 1 : 0;
}

int 
main (void)
{
  if (test_endianness () != test_endianness_vol ())
    abort ();
  exit (0);
}
