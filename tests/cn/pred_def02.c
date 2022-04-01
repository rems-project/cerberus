
struct int_list_items {
  int iv;
  struct int_list_items* next;
};

predicate {integer len} IntList(pointer l) = {
  if ( l == NULL ) {
    return { len = 0 } ;
  } else {
    let head_item = Owned<struct int_list_item>(l) ;
    let tail = IntList(head_item.value.next) ;
    return { len = tail.len + 1 } ;
  }
}
