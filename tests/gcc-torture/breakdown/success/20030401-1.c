#include "cerberus.h"
/* Testcase for PR fortran/9974.  This was a miscompilation of the g77
   front-end caused by the jump bypassing optimizations not handling
   instructions inserted on CFG edges.  */


int 
bar (void)
{
  return 1;
}

void foo (int x)
{
  unsigned char error = 0;

  if (! (error = ((x == 0) || bar ())))
    bar ();
  if (! error)
    abort ();
}

int 
main (void)
{
  foo (1);
  return 0;
}
  
