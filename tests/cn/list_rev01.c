

struct node {
  struct node *next;
  int v;
};

predicate {integer len} List (pointer p) = {
  if ( p == NULL ) {
    return { len = 0 };
  }
  else {
    let point = Owned<struct node>(p);
    let r = List (point.value.next);
    return { len = r.len + 1 };
  }
}

#define NULL ((void *)0)

[[cn::requires("List(p)")]]
[[cn::ensures("List(return)")]]
struct node *
rev_list (struct node *p) {
  struct node *rev = NULL;
  struct node *p2;

  /* FIXME: apparently we need to initialise all loop vars */
  p2 = NULL;
  pack List(NULL);
  [[cn::inv("List(p)")]]
  [[cn::inv("List(rev)")]]
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

