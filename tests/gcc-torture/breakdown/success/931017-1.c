#include "cerberus.h"
int v;

int 
h1 (void)
{
  return 0;
}

int 
h2 (int *e)
{
  if (e != &v)
    abort ();
  return 0;
}

int 
g (char *c)
{
  int i;
  int b;

  do
    {
      i = h1 ();
      if (i == -1)
	return 0;
      else if (i == 1)
	h1 ();
    }
  while (i == 1);

  do
    b = h2 (&v);
  while (i == 5);

  if (i != 2)
    return b;
  *c = 'a';

  return 0;
}


void 
f (void)
{
  char c;
  g (&c);
}

int 
main (void)
{
  f ();
  exit (0);
}


