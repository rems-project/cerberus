#include "cerberus.h"
int
sub (int i, int array[i++])
{
  return i;
}

int
main()
{
  int array[10];
  exit (sub (10, array) != 11);
}
