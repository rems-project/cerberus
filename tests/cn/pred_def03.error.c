struct int_list_items {
  int iv;
  struct int_list_items* next;
};

/*@
predicate {integer len} IntList(pointer l) {
  if ( is_null(l) ) {
    return { len: 0 } ;
  } else {
    take head_item = Owned<struct int_list_items>(l) ;
    take tail = IntList(head_item.next) ;

    assert( tail.wrong ) ;

    return { len: tail.len + 1 } ;
  }
}
@*/
