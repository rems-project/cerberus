
#include "f.h"
#include "g.h"

/* specification in f.h: f computes x mod 2 */
int f (int x)
{
  if (x < 12) {
    return x;
  }
  else {
    return g (x - 12);
  }
}

void
test_c (void) {
  int r;

  r = f (12);
  /*@ assert (r == 0i32); @*/
  r = f (25);
  /*@ assert (r == 1i32); @*/
}


