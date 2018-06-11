#include "cerberus.h"
/* Verify unaligned address aliasing on Alpha EV[45].  */

static unsigned short x, y;

void 
foo (void)
{
  x = 0x345;
  y = 0x567;
}

int 
main (void)
{
  foo ();
  if (x != 0x345 || y != 0x567)
    abort ();
  exit (0);
}
