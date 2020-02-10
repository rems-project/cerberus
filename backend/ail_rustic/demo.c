struct s {
  int f1;
  int [[rc::cell_scalar]] f2;
  struct s2 * [[rc::cell("f3get", "f3set")]] f3;
};

[[rc::forall("a")]]
[[rc::funlifetime("f")]]
[[rc::leq("f", "a")]]
void f([[rc::mut("a")]] struct s * [[rc::mut("f"),rc::nonnull]] x) {
  x->f1 = 1;
}

[[rc::forall("a")]]
[[rc::funlifetime("f")]]
[[rc::leq("f", "a")]]
void g([[rc::read("a"),rc::inited("s{f1:init,f2:notinit,f3:notinit}")]] struct s * [[rc::mut("f"),rc::nonnull]] x) {
  printf("%d\n", x->f1);
}

int main(void) {
  struct s s0;
  // s0 is nonnull
  f(&s0);
  g(&s0);
  return 0;
}
