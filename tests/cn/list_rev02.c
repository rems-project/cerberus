

struct node {
  struct node *next;
  int v;
};

predicate {integer len} List (pointer p) {
  if ( p == NULL ) {
    return { len = 0 };
  }
  else {
    let Point = Owned<struct node>(p);
    let R = List (Point.value.next);
    return { len = R.len + 1 };
  }
}

#define NULL ((void *)0)

[[cn::requires("let L = List(p)")]]
[[cn::ensures("let L2 = List(return)")]]
struct node *
rev_list (struct node *p) {
  struct node *rev = NULL;
  struct node *p2;

  /* leaving loop var uninitialised */
  pack List(NULL);
  [[cn::inv("let L_p = List(p)")]]
  [[cn::inv("let L_rev = List(rev)")]]
  while (p) {
    unpack List(p);
    p2 = p->next;
    p->next = rev;
    rev = p;
    pack List(rev);
    p = p2;
  }
  unpack List(NULL);
  return rev;
}

