// Minimised from https://github.com/rems-project/cn-tutorial/blob/main/src/examples/queue_pop.c
// Tests that CN has a work-around for https://github.com/Z3Prover/z3/issues/7352

#ifndef CN_UTILS
void *cn_malloc(unsigned long long);
void cn_free_sized(void*, unsigned long long);
#endif

struct int_queue {
  struct int_queueCell* front;
  struct int_queueCell* back;
};
struct int_queueCell {
  int first;
  struct int_queueCell* next;
};

/*@
function (boolean) eq_testable(pointer x, pointer y) {
    ptr_eq(x,y) || !addr_eq(x,y)
}

predicate (void) Test(pointer f, pointer b) {
  if (ptr_eq(f,b)) {
    take F = Owned<struct int_queueCell>(b);
    return;
  } else {
    return;
  }
}
@*/
void freeIntQueueCell (struct int_queueCell *p)
/*@ trusted;
    requires take u = Block<struct int_queueCell>(p);
    ensures true;
@*/
{
    cn_free_sized(p, sizeof(struct int_queueCell));
}

void IntQueue_pop (struct int_queue *q)
/*@
requires
    take Q = Owned<struct int_queue>(q);
    !is_null(Q.front) && !is_null(Q.back);
    eq_testable(Q.front, Q.back);
    take B = Test(Q.front, Q.back);
ensures
    take Q2 = Block<struct int_queue>(q);
@*/
{
  struct int_queueCell* h = q->front;
  if (h == q->back) {
    int x = h->first;
    freeIntQueueCell(h);
    return;
  }
}

int main()
/*@ trusted; @*/
{
    struct int_queueCell cell = { .first = 0, .next = 0 };
    struct int_queue q = { .front = &cell, .back = &cell };
    IntQueue_pop(&q);
}
