#include <stdlib.h>
/* Source: Neil Booth, from PR # 115.  */

int 
false (void)
{
  return 0;
}


int main (int argc,char *argv[])
{
  int count = 0;

  while (false() || count < -123)
    ++count;

  if (count)
    abort ();

  return 0;
}
