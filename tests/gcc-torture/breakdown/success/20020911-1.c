#include "cerberus.h"
unsigned short c = 0x8000;
int 
main (void)
{
  if ((c-0x8000) < 0 || (c-0x8000) > 0x7fff)
    abort();
  return 0;
}
