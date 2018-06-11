#include "cerberus.h"
/* The non-destructive folder was always emitting >= when folding
   comparisons to signed_max+1.  */


int 
main (void)
{
  unsigned long count = 8;

  if (count > INT_MAX)
    abort ();

  return (0);
}

