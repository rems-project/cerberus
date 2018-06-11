#include "cerberus.h"

int
foo (int x)
{
  if ((int) (x & 0x80ffffff) != (int) (0x8000fffe))
    abort ();

  return 0;
}

int 
main (void)
{
  return foo (0x8000fffe);
}
