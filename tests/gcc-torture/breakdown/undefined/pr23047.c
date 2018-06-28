#include "cerberus.h"
/* { dg-options "-fwrapv" } */
#include <limits.h>
void f(int i)
{
  i = i > 0 ? i : -i;
  if (i<0)
    return;
  abort ();
}

int main(int argc, char *argv[])
{
  f(INT_MIN);
  exit (0);
}
