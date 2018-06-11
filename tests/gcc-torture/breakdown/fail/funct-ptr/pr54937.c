#include "cerberus.h"

int a[1];
void (*terminate_me)(int);

void
t(int c)
{ int i;
  for (i=0;i<c;i++)
    {
      if (i)
       terminate_me(0);
      a[i]=0;
    }
}

int 
main (void)
{
  terminate_me = exit;
  t(100);
  abort();
}
