#include "cerberus.h"
void
sub3 (const int *i)
{
}

void
eq (int a, int b)
{
  static int i = 0;
  if (a != i)
    abort ();
  i++;
}

int 
main (void)
{
  int i;

  for (i = 0; i < 4; i++)
    {
      const int j = i;
      int k;
      sub3 (&j);
      k = j;
      eq (k, k);
    }
  exit (0);
}
