#include "cerberus.h"

struct baz {
  int a, b, c;
};

void
foo (int a, int b, int c)
{
  if (a != 4)
    abort ();
}

void
bar (struct baz x, int b, int c)
{
  foo (x.b, b, c);
}

int 
main (void)
{
  struct baz x = { 3, 4, 5 };
  bar (x, 1, 2);
  exit (0);
}
