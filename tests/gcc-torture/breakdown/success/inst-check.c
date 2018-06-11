#include "cerberus.h"

int 
f (int m)
{
  int i,s=0;
  for(i=0;i<m;i++)
    s+=i;
  return s;
}

int 
main (void)
{
  exit (0);
}
