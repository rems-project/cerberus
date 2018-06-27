#include "cerberus.h"
static inline int fu (unsigned short data)
{
  return data;
}
void
ru (int i)
{
   if(fu(i++)!=5)abort();
   if(fu(++i)!=7)abort();
}
static inline int fs (signed short data)
{
  return data;
}
void
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
