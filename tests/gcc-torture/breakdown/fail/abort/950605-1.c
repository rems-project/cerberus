#include "cerberus.h"
int 
f (int c)
{
  if (c != 0xFF)
    abort ();
}

int 
main (void)
{
  f (-1);
  exit (0);
}
