#include "cerberus.h"

void 
     test1(int i)
{
  if (i == 12)
    return;
  if (i != 17)
    {
      if (i == 15)
	return;
      abort ();
    }
}

int 
main (void) { test1 (15); return 0; }
