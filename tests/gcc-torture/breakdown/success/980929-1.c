#include "cerberus.h"
void f(int i)
{
  if (i != 1000)
    abort ();
}


int 
main (void)
{
  int n=1000;
  int i;

  f(n);
  for(i=0; i<1; ++i) {
    f(n);
    n=666;
    &n;
  }

  exit (0);
}
