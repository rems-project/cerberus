#include "cerberus.h"
unsigned char x = 50;
volatile short y = -5;

int 
main (void)
{
  x /= y;
  if (x != (unsigned char) -10)
    abort ();
  exit (0);
}
