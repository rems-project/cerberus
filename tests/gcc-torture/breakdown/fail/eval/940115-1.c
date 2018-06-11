#include "cerberus.h"
int 
f (char *cp, char *end)
{
  return (cp < end);
}

int 
main (void)
{
  if (! f ((char *) 0, (char *) 1))
    abort();
  exit (0);
}
