#include "cerberus.h"

typedef struct st {
    int a;
} ST;

int 
foo(ST *s, int c)
{
  int first = 1;
  int count = c;
  ST *item = s;
  int a = s->a;
  int x;

  while (count--)
    {
      x = item->a;
      if (first)
        first = 0;
      else if (x >= a)
        return 1;
      a = x;
      item++;
    }
  return 0;
}


int 
main (void)
{
  ST _1[2] = {{2}, {1}};
  if (foo(_1, 2) != 0)
    abort ();
  return 0;
}
