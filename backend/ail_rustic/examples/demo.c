struct s {
  int f1;
  int f2 [[rc::cell_scalar]];
  struct s2 * f3 [[rc::cell("f3get", "f3set")]];
};

[[rc::forall("a"), rc::function_lifetime("f"), rc::leq("f", "a")]]
void f([[rc::mut("a")]] struct s * [[rc::mut("f"), rc::nonnull]] p) {
  p->f1 = 1;
}

[[rc::forall("a"), rc::funtion_lifetime("f"), rc::leq("f", "a")]]
void g([[rc::read("a"), rc::inited("s{f1:init,f2:notinit,f3:notinit}")]] struct s * [[rc::mut("f"), rc::nonnull]] p) {
  int x = p->f1 + 1;
}

int main(void) {
  struct s s0;
  // s0 is nonnull, but not initialised
  f(&s0);
  // s0 now has field f1 initialised
  g(&s0);
}
