// WRC
// The final read (z3) is required to see 1.
// An exhaustive execution of this program should therefore only return the value 1.
int main() {
  atomic_int x = 0;
  atomic_int y = 0;
  int z1; int z2; int z3;

  {{{ x.store(1,mo_release);
  ||| { z1=x.load(mo_acquire).readsvalue(1);
        y.store(1,mo_release); }
  ||| { z2=y.load(mo_acquire).readsvalue(1);
        z3=x.load(mo_acquire); }
  }}}
  return z3;
}
