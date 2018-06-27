#include "cerberus.h"
typedef struct  { short x; } test;

test *p;

void g(int *a)
{
 p = (test*)a;
}

int 
f (void)
{
  int a;
  g(&a);
  a = 10;
  test s={1};
  *p=s;
  return a;
}

int 
main (void) {
  if (f() == 10)
    __builtin_abort();
  return 0;
}


