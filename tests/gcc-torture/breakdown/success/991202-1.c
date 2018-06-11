#include "cerberus.h"
int x, y;

int 
main (void)
{
  x = 2;
  y = x;
  do
    {
      x = y;
      y = 2 * y;
    }
  while ( ! ((y - x) >= 20));
  exit (0);
}

