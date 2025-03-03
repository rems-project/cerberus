struct list_head {
        struct list_head *next, *prev;
};

/*@
function (struct list_head) default_list_head ()

predicate (struct list_head) O_struct_list_head(pointer p, boolean condition)
{
  if (condition) {
    take v = RW<struct list_head>(p);
    return v;
  }
  else {
    return default_list_head ();
  }
}
@*/

void __list_del(struct list_head * prev, struct list_head * next)
/*@ requires take O1 = RW(prev);
             take O2 = O_struct_list_head(next, !ptr_eq(prev, next));
    ensures take O1R = RW(prev);
            take O2R = O_struct_list_head(next, !ptr_eq(prev, next));
            ptr_eq(prev, next) || ptr_eq(O2.next, O2R.next);
            ptr_eq(prev, next) || {(*prev).prev} unchanged;
            ptr_eq((*prev).next, next);
            ptr_eq(prev, next) || ptr_eq(O2R.prev, prev);
            !ptr_eq(prev, next) || ptr_eq((*prev).prev, prev); @*/
{
        /*@ split_case !ptr_eq(prev, next); @*/
        next->prev = prev;
        prev->next = next;
}

int main(void)
/*@ trusted; @*/
{
  struct list_head next = {.next = 0, .prev = 0};
  struct list_head prev = {.next = 0, .prev = 0};
  __list_del(&next, &prev);
}
