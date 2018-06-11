#include "cerberus.h"
typedef unsigned long long u64;
unsigned long foo = 0;
u64 f() ;

u64 
f (void) {
  return ((u64)40) + ((u64) 24) * (int)(foo - 1);
}

int 
main (void)
{
  if (f () != 16)
    abort ();
  exit (0);
}
