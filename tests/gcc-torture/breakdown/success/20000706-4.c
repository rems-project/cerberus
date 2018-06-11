#include "cerberus.h"

int *c;

void bar(int b)
{
  if (*c != 1 || b != 2)
    abort();
}

void foo(int a, int b)
{
  c = &a;
  bar(b);
}

int 
main (void)
{
  foo(1, 2);
  exit(0);
}
