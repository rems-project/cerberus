#include "cerberus.h"
double x = 0x1.fp1;
int 
main (void)
{
  if (x !=  3.875)
    abort ();
  exit (0);
}


