
#include "f.h"
#include "g.h"

int
f (int x)
{
  if (x < 12) {
    return x;
  }
  else {
    return g (x - 12);
  }
}


