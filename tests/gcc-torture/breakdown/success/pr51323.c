#include "cerberus.h"
/* PR middle-end/51323 */

struct S { int a, b, c; };
int v;

 void
foo (int x, int y, int z)
{
  if (x != v || y != 0 || z != 9)
    abort ();
}

static inline int
baz (const struct S *p)
{
  return p->b;
}

 void
bar (int x, struct S y)
{
  foo (baz (&y), 0, x);
}

int 
main (void)
{
  struct S s;
  v = 3; s.a = v - 1; s.b = v; s.c = v + 1;
  bar (9, s);
  v = 17; s.a = v - 1; s.b = v; s.c = v + 1;
  bar (9, s);
  return 0;
}
