// Rust Arc (atomic reference counter) example
#include <stdatomic.h>

#define ORIGINAL 1 // comment this line to test the new proposal

int main() {
  _Atomic(int) x = 2;
  int a = 0;
  int b = 0;
  {-{ {
    int r1 = 2;
    a = 1;
    atomic_compare_exchange_weak_explicit(&x, &r1, 1, memory_order_release, memory_order_relaxed);
    __BMC_ASSUME(r1 == 2);
  } ||| {
    int r2 = 1;
    atomic_compare_exchange_weak_explicit(&x, &r2, 0, memory_order_release, memory_order_relaxed);
    __BMC_ASSUME(r2 == 1);
    #ifdef ORIGINAL
    if (r2 == 1) {
       atomic_thread_fence(memory_order_acquire);
      a = 2;
    }
    #else
    atomic_load_explicit(&x, memory_order_acquire);
    a = 2;
    #endif
  } }-};
}

