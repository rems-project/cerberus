#include "cerberus.h"
static void *self(void *p){ return p; }

int 
f (void)
{
  struct { int i; } s, *sp;
  int *ip = &s.i;

  s.i = 1;
  sp = self(&s);
  
  *ip = 0;
  return sp->i+1;
}

int 
main (void)
{
  if (f () != 1)
    abort ();
  else
    exit (0);
}
