#include "cerberus.h"
int var = 0;

void
g (void)
{
  var = 1;
}

void
f (void)
{
  int f2 = 0;

  if (f2 == 0)
    ;

  g ();
}

int 
main (void)
{
  f ();
  if (var != 1)
    abort ();
  exit (0);
}
