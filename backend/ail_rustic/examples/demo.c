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

struct ll_node {
  int f;
  struct ll_node * next [[rc::recursive]];
};

[[rc::forall("a"), rc::function_lifetime("f"), rc::leq("f", "a")]]
void f2(struct ll_node * x [[rc::read("a")]]) {
  if (x) {
    int y = x->f;
    f2(x->next);
  }
}

// TODO: actual mutex
struct mutex {
  int taken;
};

[[rc::is_lock_function("mutex")]]
void lock(struct mutex *);
[[rc::is_unlock_function("mutex")]]
void unlock(struct mutex *);

struct lk_s {
  struct mutex m [[rc::mutex]];
  int f [[rc::owned_by("m")]];
  int * p [[rc::owned_by("m")]];
  int f2;
};

void f3(struct lk_s * x) {
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
  struct mutex m [[rc::mutex]];
  int f [[rc::owned_by("m")]];
  struct ll_lk_node * next [[rc::recursive, rc::owned_by("m")]];
};

int main(void) {
  struct s s0;
  // s0 is nonnull, but not initialised
  f(&s0);
  // s0 now has field f1 initialised
  g(&s0);
}
