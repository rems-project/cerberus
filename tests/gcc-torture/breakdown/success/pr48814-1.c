#include "cerberus.h"

int arr[] = {1,2,3,4};
int count = 0;

int 
incr (void)
{
  return ++count;
}

int 
main (void)
{
  arr[count++] = incr ();
  if (count != 2 || arr[count] != 3)
    abort ();
  return 0;
}
