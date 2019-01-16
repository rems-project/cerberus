/* The coherence axioms CoWW and CoWR forbid that the load reads from
   the first write.  The only allowed outcome is therefore 1. 
*/

#include <stdatomic.h>
int main() {
  _Atomic(int) x;

  atomic_store_explicit(&x, 0, memory_order_release);
  atomic_store_explicit(&x, 1, memory_order_release);
 
  assert (atomic_load_explicit(&x, memory_order_acquire) == 1); 
  
  return x;
}

