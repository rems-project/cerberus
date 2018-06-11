#include "cerberus.h"
struct X { int *p; } x;

struct X 
foo(int *p) { struct X x; x.p = p; return x; }

void __attribute((noinline))
bar() { *x.p = 1; }

int 
main (void)
{
  int i = 0;
  x = foo(&i);
  bar();
  if (i != 1)
    abort ();
  return 0;
}
