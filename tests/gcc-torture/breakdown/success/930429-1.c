#include "cerberus.h"
char *
f (char *p)
{
  short x = *p++ << 16;
  return p;
}

int 
main (void)
{
  char *p = "";
  if (f (p) != p + 1)
    abort ();
  exit (0);
}
