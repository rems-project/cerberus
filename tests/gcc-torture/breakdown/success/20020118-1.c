#include "cerberus.h"
/* This tests an insn length of sign extension on h8300 port.  */


volatile signed char *q;
volatile signed int n;

void
foo (void)
{
  signed char *p;

  for (;;)
    {
      p = (signed char *) q; n = p[2];
      p = (signed char *) q; n = p[2];
      p = (signed char *) q; n = p[2];
      p = (signed char *) q; n = p[2];
      p = (signed char *) q; n = p[2];
      p = (signed char *) q; n = p[2];
      p = (signed char *) q; n = p[2];
      p = (signed char *) q; n = p[2];
      p = (signed char *) q; n = p[2];
      p = (signed char *) q; n = p[2];
      p = (signed char *) q; n = p[2];
    }
}

int 
main (void)
{
  exit (0);
}
