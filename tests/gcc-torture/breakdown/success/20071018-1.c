#include "cerberus.h"

struct foo {
  int rank;
  char *name;
};

struct mem {
  struct foo *x[4];
};

void  bar(struct foo **f)
{
  *f = __builtin_malloc(sizeof(struct foo));
}
struct foo *  foo(int rank)
{
  void *x = __builtin_malloc(sizeof(struct mem));
  struct mem *as = x;
  struct foo **upper = &as->x[rank * 8 - 5];
  *upper = 0;
  bar(upper);
  return *upper;
}

int 
main (void)
{
  if (foo(1) == 0)
    abort ();
  return 0;
}
