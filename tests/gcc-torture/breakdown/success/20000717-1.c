#include "cerberus.h"
typedef struct trio { int a, b, c; } trio;

int
bar (int i, trio t)
{
  if (t.a == t.b || t.a == t.c)
    abort ();
  return 0;
}

int
foo (trio t, int i)
{
  return bar (i, t);
}

int 
main (void)
{
  trio t = { 1, 2, 3 };

  foo (t, 4);
  exit (0);
}
