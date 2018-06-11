#include "cerberus.h"
int a;
int 
main (void)
{
  int b = 0;
  while (a < 0 || b)
    {
      b = 0;
      for (; b < 9; b++)
	;
    }
  exit (0);
}
