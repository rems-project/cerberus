#include "cerberus.h"

static void something(int i);

int 
main (void)
{
  something(-1);
  return 0;
}

static void something(int i)
{
  if (i != -1)
    abort ();
}
