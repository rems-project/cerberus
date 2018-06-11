#include "cerberus.h"
int 
foo (char *bufp)
{
    int x = 80;
    return (*bufp++ = x ? 'a' : 'b');
}

int 
main (void)
{
  char x;

  if (foo (&x) != 'a')
    abort ();

  exit (0);
}
