#include "cerberus.h"


volatile unsigned int i;

int
main (void)
{
  unsigned char z = 0;

  do ++i;
  while (--z > 0);
  if (i != UCHAR_MAX + 1U)
    abort ();
  exit (0);
}
