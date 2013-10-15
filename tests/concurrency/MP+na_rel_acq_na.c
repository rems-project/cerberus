// MP+na_rel+acq_na
// Message Passing, of data held in non-atomic x, with release/acquire synchronisation on y.
// If the value of z1 is 1, then the value of z2 should also be 1.
// An exhaustive execution of this program should therefore return the value 1 and 2, but not 0.

#include <stdatomic.h>
int main() {
  int x=0; 
  atomic_int y=0; 
  int z1, z2;
  z2 = 2;
  {{{ { x = 1;
        atomic_store_explicit(&y, 1, memory_order_release); }
  ||| { z1 = atomic_load_explicit(&y, memory_order_acquire);
        if z1 == 1 then z2 = x; }  }}};
  return z2;
}

