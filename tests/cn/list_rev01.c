

struct node {
  struct node *next;
  int v;
};

/*@
predicate {integer len} List (pointer p) {
  if ( is_null(p) ) {
    return { len: 0 };
  }
  else {
    take Point = Owned<struct node>(p);
    assert (is_null(Point.next) || !addr_eq(Point.next, NULL));
    take R = List (Point.next);
    return { len: R.len + 1 };
  }
}
@*/

#define NULL ((void *)0)

struct node *
rev_list (struct node *p)
/*@ requires is_null(p) || !addr_eq(p, NULL); @*/
/*@ requires take R = List(p); @*/
/*@ ensures take R2 = List(return); @*/
{
  struct node *rev = NULL;
  struct node *p2;

  /* FIXME: apparently we need to initialise all loop vars */
  p2 = NULL;
  while (p)
  /*@ inv is_null(p) || !addr_eq(p, NULL); @*/
  /*@ inv is_null(rev) || !addr_eq(rev, NULL); @*/
  /*@ inv take R2 = List(p); @*/
  /*@ inv take R3 = List(rev); @*/
  {
    p2 = p->next;
    p->next = rev;
    rev = p;
    p = p2;
  }
  return rev;
}

int main(void)
/*@ trusted; @*/
{
  struct node n3 = {.next = NULL, .v = 3};
  struct node n2 = {.next = &n3, .v = 2};
  struct node n1 = {.next = &n2, .v = 1};
  struct node *rev = rev_list(&n1);
}
