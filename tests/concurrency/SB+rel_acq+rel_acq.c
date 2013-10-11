// SB+rel_acq+rel_acq
// Store Buffering (or Dekker's), with release-acquire pairs
// The reads can both see 0 in the same execution. 
// An exhaustive execution of this program should therefore return the values 0, 1, 2, 3.
int main() {
  atomic_int x=0; atomic_int y=0; int z1; int z2;
  {{{ { y.store(1,memory_order_release);
        z1=x.load(memory_order_acquire); }
  ||| { x.store(1,memory_order_release);
        z2=y.load(memory_order_acquire); }  }}}
  return z1 + (2 * z2);
}

