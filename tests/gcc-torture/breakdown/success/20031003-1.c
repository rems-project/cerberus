#include "cerberus.h"
/* PR optimization/9325  */



int 
f1 (void)
{
  return (int)2147483648.0f;
}

int 
f2 (void)
{
  return (int)(float)(2147483647);
}

int 
main (void)
{
#if INT_MAX == 2147483647
  if (f1() != 2147483647)
    abort ();
#ifdef __SPU__
  /* SPU float rounds towards zero.  */
  if (f2() != 0x7fffff80)
    abort ();
#else
  if (f2() != 2147483647)
    abort ();
#endif
#endif
  return 0;
}

