#include "cerberus.h"
typedef int new_int ;
struct S { int x; };
 
int 
main (void)
{
  if (sizeof(struct S) != sizeof(int))
    abort ();
  return 0;
}
