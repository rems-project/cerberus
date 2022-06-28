// example for testing the predicate definition frontend

struct T {
  int something;
};

predicate {integer out1} OtherPred (pointer p) {
  return { out1 = 42 } ;
}

predicate {integer z, integer out2} MyPred (pointer p, integer n) {
  if ( n == 10 ) {
    let Foo = Owned<struct T>(p) ;
    return { z = 42, out2 = 55 } ;
  } else {
    let R = MyPred(p, n + 10) ;
    let x = n + R.z + R.out2 ;
    return { z = n + 100, out2 = 55 } ;
  }
}


struct int_list_items {
  int iv;
  struct int_list_items* next;
};


predicate {list<integer> v} IntList(pointer l) {
  if ( l == NULL ) {
    return { v = nil(integer) } ;
  } else {
    let Head_item = Owned<struct int_list_items>(l) ;
    let Tail = IntList(Head_item.value.next) ;
    return { v = cons(Head_item.value.iv, Tail.v) } ;
  }
}
