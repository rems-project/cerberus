#include "cerberus.h"

void do_exit (void) { exit (0); }
void do_abort (void) { abort (); }

void foo (int x, int a)
{
  if (x < a)
    goto doit;
  do_exit ();
  if (x != a)
    goto doit;

  /* else */
  do_abort ();
  return;

doit:
  do_abort ();
}

int main()
{
  foo (1, 0);
  return 0;
}
