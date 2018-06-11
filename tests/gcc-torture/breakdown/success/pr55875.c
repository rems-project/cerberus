#include "cerberus.h"
int a[251];

int
t(int i)
{
  if (i==0)
    exit(0);
  if (i>255)
    abort ();
  return 0;
}
int 
main (void)
{
  unsigned int i;
  for (i=0;;i++)
    {
      a[i]=t((unsigned char)(i+5));
    }
}
