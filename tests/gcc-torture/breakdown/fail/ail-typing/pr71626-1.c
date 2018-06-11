#include "cerberus.h"
/* PR middle-end/71626 */

typedef __INTPTR_TYPE__ V ;

 V
foo ()
{
  V v = { (__INTPTR_TYPE__) foo };
  return v;
}

int 
main (void)
{
  V v = foo ();
  if (v[0] != (__INTPTR_TYPE__) foo)
    __builtin_abort ();
  return 0;
}
