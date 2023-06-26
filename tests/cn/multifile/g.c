
#include "f.h"
#include "g.h"

int
g (int x)
{
  if (x < 12) {
    return x;
  }
  else {
    return f (x - 12);
  }
}

