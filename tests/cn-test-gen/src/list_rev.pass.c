struct int_list {
  int head;
  struct int_list* tail;
};

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}

predicate (datatype seq) IntList(pointer p) {
  if (is_null(p)) {
    return Seq_Nil{};
  } else {
    take H = Owned<struct int_list>(p);
    take tl = IntList(H.tail);
    return (Seq_Cons { head: H.head, tail: tl });
  }
}

function [rec] (datatype seq) append(datatype seq xs, datatype seq ys) {
  match xs {
    Seq_Nil {} => {
      ys
    }
    Seq_Cons {head : h, tail : zs}  => {
      Seq_Cons {head: h, tail: append(zs, ys)}
    }
  }
}

function [rec] (datatype seq) snoc(datatype seq xs, i32 y) {
  match xs {
    Seq_Nil {} => {
      Seq_Cons {head: y, tail: Seq_Nil{}}
    }
    Seq_Cons {head: x, tail: zs}  => {
      Seq_Cons{head: x, tail: snoc (zs, y)}
    }
  }
}

function [rec] (datatype seq) rev(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : h, tail : zs}  => {
      snoc (rev(zs), h)
    }
  }
}
@*/

struct int_list* IntList_rev_aux(struct int_list* xs, struct int_list* ys)
  /*@ requires take L1 = IntList(xs); @*/
  /*@ requires take L2 = IntList(ys); @*/
  /*@ ensures take R = IntList(return); @*/
  /*@ ensures R == append(rev(L2), L1); @*/
{
  if (ys == 0) {
    return xs;
  }
  else {
    struct int_list* tmp = ys->tail;
    ys->tail = xs;
    return IntList_rev_aux(ys, tmp);
  }
}

struct int_list* IntList_rev(struct int_list* xs)
  /*@ requires take L1 = IntList(xs); @*/
  /*@ ensures take L1_rev = IntList(return); @*/
  /*@ ensures L1_rev == rev(L1); @*/
{
  return IntList_rev_aux(0, xs);
}
