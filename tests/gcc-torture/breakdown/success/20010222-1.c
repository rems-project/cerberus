#include "cerberus.h"
int a[2] = { 18, 6 };

int 
main (void)
{
  int b = (-3 * a[0] -3 * a[1]) / 12;
  if (b != -6)
    abort ();
  exit (0);
}
