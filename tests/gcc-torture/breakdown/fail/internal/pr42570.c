#include "cerberus.h"
typedef unsigned char uint8_t;
uint8_t foo[1][0];
int 
main (void)
{
  if (sizeof (foo) != 0)
    abort ();
  return 0;
}
