#include "cerberus.h"
int 
foo (char *p)
{
  int h = 0;
  do
    {
      if (*p == '\0')
	break;
      ++h;
      if (p == 0)
	abort ();
      ++p;
    }
  while (1);
  return h;
}
int 
main (void)
{
  if (foo("a") != 1)
    abort ();
  return 0;
}
