// example for testing the predicate definition frontend

struct T {
  int something;
};

/*@
predicate {integer out1} OtherPred (pointer p) {
  return { out1: 42 } ;
}

predicate {integer z, integer out2} MyPred (pointer p, integer n) {
  if ( n == 10 ) {
    take Foo = Owned<struct T>(p) ;
    return { z: 42, out2: 55 } ;
  } else {
    take R = MyPred(p, n + 10) ;
    let x = n + R.z + R.out2 ;
    return { z: n + 100, out2: 55 } ;
  }
}
@*/

struct int_list_items {
  int iv;
  struct int_list_items* next;
};

/*@
datatype int_list {
  Nil {},
  Cons {i32 x, datatype int_list tl}
}

predicate {datatype int_list v} IntList(pointer l) {
  if ( is_null(l) ) {
    return { v: Nil {} } ;
  } else {
    take H = Owned<struct int_list_items>(l) ;
    take T = IntList(H.next) ;
    return { v: Cons {x: H.iv, tl: T.v} } ;
  }
}
@*/

int main(void)
{
}
