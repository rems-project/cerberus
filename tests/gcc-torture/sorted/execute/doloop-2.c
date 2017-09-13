#include "cerberus.h"


volatile unsigned int i;

int
main (void)
{
  unsigned short z = 0;

  do ++i;
  while (--z > 0);
  if (i != USHRT_MAX + 1U)
    abort ();
  exit (0);
}
