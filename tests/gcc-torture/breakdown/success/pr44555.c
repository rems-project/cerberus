#include "cerberus.h"
struct a {
    char b[100];
};
int foo(struct a *a)
{
  if (&a->b)
    return 1;
  return 0;
}
int 
main (void)
{
  if (foo((struct a *)0) != 0)
    abort ();
  return 0;
}
