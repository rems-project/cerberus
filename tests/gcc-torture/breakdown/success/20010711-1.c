#include "cerberus.h"
void foo (int *a) {}

int 
main (void)
{
  int a;
  if (&a == 0)
    abort ();
  else
    {
      foo (&a);
      exit (0);
    }
}
