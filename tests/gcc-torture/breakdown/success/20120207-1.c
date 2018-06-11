#include "cerberus.h"
/* PR middle-end/51994 */
/* Testcase by Uros Bizjak <ubizjak@gmail.com> */

extern char *strcpy (char *, const char *);

char 
test (int a)
{
  char buf[16];
  char *output = buf;

  strcpy (&buf[0], "0123456789");

  output += a;
  output -= 1;

  return output[0];
}

int 
main (void)
{
  if (test (2) != '1')
    abort ();

  return 0;
}
