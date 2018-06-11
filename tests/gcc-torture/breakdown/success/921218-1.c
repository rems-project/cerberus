#include "cerberus.h"
int 
f (void)
{
  return (unsigned char)("\377"[0]);
}

int 
main (void)
{
  if (f() != (unsigned char)(0377))
    abort();
  exit (0);
}
