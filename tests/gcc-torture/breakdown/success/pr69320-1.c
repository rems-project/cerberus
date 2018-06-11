#include "cerberus.h"
int a, b, d, f;
char c;
static int *e = &d;
int 
main (void) {
  int g = -1L;
  *e = g;
  c = 4;
  for (; c >= 14; c++)
    *e = 1;
  f = a == 0;
  *e ^= f;
  int h = ~d;
  if (d)
    b = h;
  if (h)
    exit (0);
  abort ();
}

