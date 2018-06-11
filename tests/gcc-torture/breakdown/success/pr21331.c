#include "cerberus.h"

int bar (void) {  return -1;  }

unsigned long 
foo (void)
{ unsigned long retval;
  retval = bar ();
  if (retval == -1)  return 0;
  return 3;  }

int 
main (void)
{ if (foo () != 0)  abort ();
  return 0;  }

