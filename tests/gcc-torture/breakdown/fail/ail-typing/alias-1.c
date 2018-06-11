#include "cerberus.h"
int val;

int *ptr = &val;
float *ptr2 = &val;


int 
typepun (void)
{
  *ptr2=0;
}

int 
main (void)
{
  *ptr=1;
  typepun ();
  if (*ptr)
    __builtin_abort ();
}

