#include "cerberus.h"
int 
main (void)
{
  short ssi = 126;
  unsigned short usi = 65280;
  int fail = !(ssi < usi);
  if (fail)
    abort ();
  return 0;
}

