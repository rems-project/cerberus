#include "cerberus.h"
/* "i" overflows in f().  Check that x[i] is not treated as a giv.  */

#if CHAR_BIT == 8

void f (unsigned int *x)
{
  unsigned char i;
  int j;

  i = 0x10;
  for (j = 0; j < 0x10; j++)
    {
      i += 0xe8;
      x[i] = 0;
      i -= 0xe7;
    }
}

int 
main (void)
{
  unsigned int x[256];
  int i;

  for (i = 0; i < 256; i++)
    x[i] = 1;
  f (x);
  for (i = 0; i < 256; i++)
    if (x[i] != (i >= 0x08 && i < 0xf8))
      abort ();
  exit (0);
}
#else
int 
main (void) { exit (0); }
#endif
