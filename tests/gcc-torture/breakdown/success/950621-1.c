#include "cerberus.h"
struct s
{
  int a;
  int b;
  struct s *dummy;
};

int
f (struct s *sp)
{
  return sp && sp->a == -1 && sp->b == -1;
}

int 
main (void)
{
  struct s x;
  x.a = x.b = -1;
  if (f (&x) == 0)
    abort ();
  exit (0);
}
