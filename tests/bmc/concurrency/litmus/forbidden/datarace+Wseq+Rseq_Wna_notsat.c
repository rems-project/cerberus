#include <stdatomic.h>
int main() {
  _Atomic(int) x=2;
  int y = 0;
  {-{ { atomic_store_explicit(&x, 3, memory_order_seq_cst); }
  ||| { y = (atomic_load_explicit(&y, memory_order_seq_cst) == 3); }  
  }-};
  return 0;
}

