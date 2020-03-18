struct s {
  int f1;
  int f2;
  struct s2 *f3;
};

void f(struct s *p) {
  p->f1 = 1;
}

void g(struct s *p) {
  int x = p->f1 + 1;
}

struct ll_node {
  int f;
  struct ll_node *next;
};

void f2(struct ll_node *x) {
  if (x) {
    int y = x->f;
    f2(x->next);
  }
}

// TODO: actual mutex
struct mutex {
  int taken;
};

void lock(struct mutex *);
void unlock(struct mutex *);

struct lk_s {
  struct mutex m;
  int f;
  int *p;
  int f2;
};

[[forall("asd"), exists("asd2")]]
void f3(struct lk_s *x) {
  if (x) {
    lock(&x->m);
    int y = x->f;
    if (x->p) {
      int z = *x->p;
    }
    unlock(&x->m);
    // can't access f or p
    int w = x->f2;
  }
}

struct ll_lk_node {
  struct mutex m;
  int f;
  struct ll_lk_node *next;
};

void f4() {
  int x; // owns something of size |int|
  int y = x + 1;
}

void f5(int *x) {
  // after the following statement, one of `x` and `y` has to be a pointer what `x` was a pointer to
  // the other's value should not be "used" (or at least, not used to dereference)
  int *y = x; 
  int z = *y; // it has to be `y`
}

int main(void) {
  struct s s0;
  // s0 is nonnull, but not initialised
  f(&s0);
  // s0 now has field f1 initialised
  g(&s0);
}
