#include "cerberus.h"
/* PR ipa/78791 */

int val;

int *ptr = &val;
float *ptr2 = &val;

static void
typepun (void)
{
  *ptr2=0;
}

int 
main (void)
{
  *ptr=1;
  typepun ();
  if (*ptr)
    __builtin_abort ();
}
