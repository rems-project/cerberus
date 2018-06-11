#include "cerberus.h"
int 
main (void)
{
  int v = 42;

  inline int fff (int x)
    {
      return x*10;
    }

  return (fff (v) != 420);
}
