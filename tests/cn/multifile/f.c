
#include "f.h"
#include "g.h"

int
f (int x)
/*@ requires x >= 0 @*/
/*@ ensures return == (mod (x, 12)) @*/
{
  if (x < 12) {
    return x;
  }
  else {
    return g (x - 12);
  }
}


