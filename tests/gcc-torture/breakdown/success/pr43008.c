#include "cerberus.h"
int i;
struct X {
  int *p;
};
struct X * 
my_alloc (void)
{
  struct X *p = __builtin_malloc (sizeof (struct X));
  p->p = &i;
  return p;
}
int 
main (void)
{
  struct X *p, *q;
  p = my_alloc ();
  q = my_alloc ();
  *(p->p) = 1;
  *(q->p) = 0;
  if (*(p->p) != 0)
    abort ();
  return 0;
}
