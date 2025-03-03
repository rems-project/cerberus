struct int_list_items {
  int iv;
  struct int_list_items* next;
};

/*@
predicate {integer len} IntList(pointer l) {
  if ( is_null(l) ) {
    return { len: 0 } ;
  } else {
    take Head_item = RW<struct int_list_items>(l) ;
    take Tail = IntList(Head_item.next) ;
    return { len: Tail.len + 1 } ;
  }
}
@*/

int main(void)
{
}
