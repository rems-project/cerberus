#include "cerberus.h"
int v = 3;

void
f ()
{
  int v = 4;
  {
    extern int v;
    if (v != 3)
      abort ();
  }
}

int
main ()
{
  f ();
  exit (0);
}
