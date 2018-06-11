#include "cerberus.h"
/* PR rtl-optimization/47299 */


 unsigned short
foo (unsigned char x)
{
  return x * 255;
}

int 
main (void)
{
  if (foo (0x40) != 0x3fc0)
    abort ();
  return 0;
}
