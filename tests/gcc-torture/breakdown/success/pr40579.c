#include "cerberus.h"
static char * 
itos(int num)
{
  return (char *)0;
}
static void 
foo(int i, const char *x)
{
  if (i >= 4)
    abort ();
}
int 
main (void)
{
  int x = -__INT_MAX__ + 3;
  int i;

  for (i = 0; i < 4; ++i)
    {
      char *p;
      --x;
      p = itos(x);
      foo(i, p);
    }

  return 0;
}

