#include "cerberus.h"

extern void link_error (void);

static int ok = 0;

void bar (void)
{
  ok = 1;
}

void foo(int x)
{
  switch (x)
  {
  case 0:
    if (0)
    {
      link_error();
  case 1:
      bar();
    }
  }
}

int 
main (void)
{
  foo (1);
  if (!ok)
    abort ();
  return 0;
}

