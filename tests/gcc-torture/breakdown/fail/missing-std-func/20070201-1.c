#include "cerberus.h"
/* PR middle-end/30473 */

char *
foo (char *buf, char *p)
{
  sprintf (buf, "abcde", p++);
  return p;
}

int
main (void)
{
  char buf[6];
  if (foo (buf, &buf[2]) != &buf[3])
    abort ();
  return 0;
}
