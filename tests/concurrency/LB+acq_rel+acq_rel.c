// LB+acq_rel+acq_rel
// Load Buffering, with acquire/release pairs
// The values of z1 and z2 cannot both be 1. They can be both 0, or one of them can be 1.
// An exhaustive execution of this program should therefore return the values 0, 1 and 2.

#include <stdatomic.h>
int main() {
  _Atomic int x=0, y=0;
  int z1, z2;
  // Because of a bug in the parser, we have to declare the pointers explicitely
  {{{ { z1 = atomic_load_explicit(&x, memory_order_acquire); 
        atomic_store_explicit(&y, 1, memory_order_release); }
  ||| { z2 = atomic_load_explicit(&y, memory_order_acquire);
        atomic_store_explicit(&x, 1, memory_order_release); }  }}};
  return z1 + (2 * z2);
}

