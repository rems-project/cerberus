// IRIW with release/acquire
// The reading threads do not have to see the writes to x and y in the same order.
// An exhaustive execution of this program should therefore only return the value 0 (instead of blocking?).
int main() {
  atomic_int x = 0; atomic_int y = 0;
  int z1; int z2; int z3; int z4;
  {{{ x.store(1, memory_order_release);
  ||| y.store(1, memory_order_release);
  ||| { z1=x.load(memory_order_acquire).readsvalue(1);
        z2=y.load(memory_order_acquire).readsvalue(0); }
  ||| { z3=y.load(memory_order_acquire).readsvalue(1);
        z4=x.load(memory_order_acquire).readsvalue(0); }
  }}};
  return 0; }

