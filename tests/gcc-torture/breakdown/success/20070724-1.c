#include "cerberus.h"

static unsigned char magic[] = "\235";
static unsigned char value = '\235';

int 
main (void)
{
  if (value != magic[0])
    abort ();
  return 0;
}
