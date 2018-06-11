#include "cerberus.h"
unsigned int a[0x1000];
extern const unsigned long v;

void 
f (unsigned long a)
{
  if (a != 0xdeadbeefL)
    abort();
}

int 
main (void)
{
  f (v);
  f (v);
  exit (0);
}

const unsigned long v = 0xdeadbeefL;
