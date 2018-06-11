#include "cerberus.h"
int bar(int foo)
{
  return (int)(((unsigned long long)(long long)foo) / 8);
}
int 
main (void)
{
  if (sizeof (long long) > sizeof (int)
      && bar(-1) != -1)
    abort ();
  return 0;
}
