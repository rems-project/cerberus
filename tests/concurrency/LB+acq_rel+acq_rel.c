// LB+acq_rel+acq_rel
// Load Buffering, with acquire/release pairs
// The values of z1 and z2 cannot both be 1. They can be both 0, or one of them can be 1.
// An exhaustive execution of this program should therefore return the values 0, 1 and 2.
int main() {
  atomic_int x=0; atomic_int y=0; int z1; int z2;
  {{{ { z1=x.load(memory_order_acquire); 
        y.store(1,memory_order_release); }
  ||| { z2=y.load(memory_order_acquire);
        x.store(1,memory_order_release); }  }}}
  return z1 + (2 * z2);
}
