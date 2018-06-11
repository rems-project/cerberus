#include "cerberus.h"

int
wwrite(long long i)
{
  switch(i)
    {
    case 3:
    case 10:
    case 23:
    case 28:
    case 47:
      return 0;
    default:
      return 123;
    }
}

int 
main (void)
{
  if (wwrite((long long) 0) != 123)
    abort();
  exit(0);
}

