
#include "f.h"
#include "g.h"

int
g (int x)
/*@ requires x >= 0 @*/
/*@ ensures return == (mod (x, 12)) @*/
{
  if (x < 12) {
    return x;
  }
  else {
    return f (x - 12);
  }
}

