#include "cerberus.h"
short a = -1;
int b;
char c;

int 
main (void)
{
  c = a;
  b = a | c;
  if (b != -1)
    __builtin_abort ();
  return 0;
}
