#include "cerberus.h"
struct s { char c1, c2; };
void foo (struct s s)
{
  static struct s s1;
  s1 = s;
}
int 
main (void)
{
  static struct s s2;
  foo (s2);
  exit (0);
}
