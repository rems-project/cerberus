#include "cerberus.h"
/* PR middle-end/53084 */


 void
bar (const char *p)
{
  if (p[0] != 'o' || p[1] != 'o' || p[2])
    abort ();
}

int 
main (void)
{
  static const char *const foo[] = {"foo" + 1};
  bar (foo[0]);
  return 0;
}
