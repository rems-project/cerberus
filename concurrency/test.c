
int main() {
  atomic_int x=0; atomic_int y=0;
  {{{ { y.store(1,memory_order_release);
          r1=x.load(memory_order_acquire); }
  ||| { x.store(1,memory_order_release);
          r2=y.load(memory_order_acquire); }  }}}
  return 0;
}
