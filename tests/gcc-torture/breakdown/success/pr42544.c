#include "cerberus.h"
/* PR c/42544 */


int 
main (void)
{
  signed short s = -1;
  if (sizeof (long long) == sizeof (unsigned int))
    return 0;
  if ((unsigned int) s >= 0x100000000ULL)
    abort ();
  return 0;
}
