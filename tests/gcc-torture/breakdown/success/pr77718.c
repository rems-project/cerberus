#include "cerberus.h"
/* PR middle-end/77718 */

char a[64] ;

 int
foo (void)
{
  return __builtin_memcmp ("bbbbbb", a, 6);
}

 int
bar (void)
{
  return __builtin_memcmp (a, "bbbbbb", 6);
}

int 
main (void)
{
  __builtin_memset (a, 'a', sizeof (a));
  if (((foo () < 0) ^ ('a' > 'b'))
      || ((bar () < 0) ^ ('a' < 'b')))
    __builtin_abort ();
  return 0;
}
