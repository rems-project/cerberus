// example for testing the predicate definition frontend

struct T {
  int something;
};

predicate {integer out1} OtherPred (pointer p) = {
  return { out1 = 42 } ;
}

predicate {integer z, integer out2} MyPred (pointer p, integer n) = {
  if ( n == 10 ) {
    let foo = Owned<struct T>(p) ;
    return { z = 42, out2 = 55 } ;
  } else {
    let r = MyPred(p, n + 10) ;
    let x = n + r.z + r.out2 ;
    return { z = n + 100, out2 = 55 } ;
  }
}


struct int_list_items {
  int value;
  struct int_list_items* next;
};

/*
TODO: list syntax is not done yet

predicate {list<integer> v} IntList(pointer l) = {
  if ( l == NULL ) {
    return { v = [] } ;
  } else {
    let head_item = Owned<struct int_list_item>(l) ;
    let tail = IntList(head_item.next) ;
    return { v = head_item.value :: tail.v } ;
  }
}
*/