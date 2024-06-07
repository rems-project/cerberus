/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}

@*/

struct int_queueCell {
  int first;
  struct int_queueCell* next;
};

/*@
predicate (datatype seq) IntQueueCell(pointer head, pointer tail, i32 last) {
  if (ptr_eq(head, tail)) {
    return Seq_Cons { head: last, tail: Seq_Nil{} };
  } else {
    take HD = Owned<struct int_queueCell>(head);
    assert (head != HD.next);
    take Rest = IntQueueCell(HD.next, tail, last);
    return Seq_Cons { head: HD.first, tail: Rest };
  }
}

@*/

void IntQueue_push (int x, struct int_queueCell *head, struct int_queueCell *tail)
/*@
requires
  take Q = IntQueueCell(head, tail, 0i32);
ensures
  take Q2 = IntQueueCell(head, tail, 1i32);
@*/
{
}
