#include "cerberus.h"
void foo(int *p)
{
  int x;
  int y;
  x = *p;
  *p = 0;
  y = *p;
  if (x != y)
    return;
  abort ();
}

int 
main (void)
{
  int a = 1;
  foo(&a);
  return 0;
}
