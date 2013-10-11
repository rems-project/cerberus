// MP+na_rel+acq_na
// Message Passing, of data held in non-atomic x, with release/acquire synchronisation on y.
// If the value of z1 is 1, then the value of z2 should also be 1.
// An exhaustive execution of this program should therefore only return the value 1.
int main() {
  int x=0; atomic_int y=0; int z1; int z2;
  {{{ { x=1;
        y.store(1,memory_order_release); }
  ||| { z1=y.load(memory_order_acquire).readsvalue(1);
        z2=x; }  }}}
  return z2;
}

