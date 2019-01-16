/* The coherence axioms CoWW and CoWR forbid that the load reads from
   the first write.  The only allowed outcome is therefore 1. The
   diference with the test coherence+rel_rel_acq is that a thread is
   created between the first and second write, and the test will only
   succeed if the operational semantics creates the correct asw edges.
*/

#include <stdatomic.h>
int main() {
  _Atomic(int) x;
  atomic_store_explicit(&x, 0, memory_order_release);
  {-{ { atomic_store_explicit(&x, 1, memory_order_release);
        assert (atomic_load_explicit(&x, memory_order_acquire) == 0); }
  ||| {  }  }-};
  
  return x;
}

