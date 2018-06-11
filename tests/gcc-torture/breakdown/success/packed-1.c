#include "cerberus.h"
short x1 = 17;

struct
{
  short i __attribute__((packed));
} t;

void
f (void)
{
  t.i = x1;
  if (t.i != 17)
    abort ();
}

int 
main (void)
{
  f ();
  exit (0);
}
