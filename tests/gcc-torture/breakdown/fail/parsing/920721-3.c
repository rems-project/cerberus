#include "cerberus.h"
static inline fu (unsigned short data)
{
  return data;
}
int 
ru (int i)
{
   if(fu(i++)!=5)abort();
   if(fu(++i)!=7)abort();
}
static inline fs (signed short data)
{
  return data;
}
int 
rs (int i)
{
   if(fs(i++)!=5)abort();
   if(fs(++i)!=7)abort();
}


int 
main (void)
{
  ru(5);
  rs(5);
  exit(0);
}
