// WRC
// The final read (z3) is required to see 1.
// An exhaustive execution of this program should therefore only return the value 1.
//
//
#include <stdatomic.h>

int main() {
  _Atomic(int) x = 0, y = 0;
  int z1; int z2; int z3;

  {-{ { atomic_store_explicit(&x,1,memory_order_release); }
  ||| { __BMC_ASSUME(atomic_load_explicit(&x, memory_order_acquire) == 1);
        atomic_store_explicit(&y, 1, memory_order_release); }
  ||| { __BMC_ASSUME(atomic_load_explicit(&y, memory_order_acquire) == 1);
        z3 = atomic_load_explicit(&x, memory_order_acquire);
      }
  }-}
  return z3;
}
