#include "cerberus.h"
int bar = 0;

void
f (int *p)
{
  int foo = 2;

  while (foo > bar)
    {
      foo -=  bar;
      *p++ = foo;
      bar = 1;
    }
}

int 
main (void)
{
  int tab[2];
  tab[0] = tab[1] = 0;
  f (tab);
  if (tab[0] != 2 || tab[1] != 1)
    abort ();
  exit (0);
}
