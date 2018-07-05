#include "cerberus.h"
char buf[10];

int 
main (void)
{
  int l = sprintf (buf, "foo\0bar");
  if (l != 3)
    abort ();
  return 0;
}

