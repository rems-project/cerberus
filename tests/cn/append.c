struct int_list { 
  int head;
  struct int_list* tail;
};

/*@
datatype seq { 
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
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

predicate (datatype seq) IntList(pointer p) {
  if (is_null(p)) { 
    return Seq_Nil{};
  } else { 
    take H = Owned<struct int_list>(p);
    assert (is_null(H.tail) || (u64)H.tail != 0u64);
    take tl = IntList(H.tail);
    return (Seq_Cons { head: H.head, tail: tl });
  }
}
@*/

struct int_list* IntList_append(struct int_list* xs, struct int_list* ys) 
/*@ requires is_null(xs) || !addr_eq(xs, NULL); @*/
/*@ requires is_null(ys) || !addr_eq(ys, NULL); @*/
/*@ requires take L1 = IntList(xs); @*/
/*@ requires take L2 = IntList(ys); @*/
/*@ ensures is_null(return) || !addr_eq(return, NULL); @*/
/*@ ensures take L3 = IntList(return); @*/
/*@ ensures L3 == append(L1, L2); @*/
{ 
  if (xs == 0) { 
    /*@ unfold append(L1, L2); @*/
    return ys;
  } else { 
    /*@ unfold append(L1, L2); @*/
    struct int_list *new_tail = IntList_append(xs->tail, ys);
    xs->tail = new_tail;
    return xs;
  }
}

/*@
function [rec] ({datatype seq fst, datatype seq snd}) split_cn(datatype seq xs) 
{
  match xs {
    Seq_Nil {} => { 
      {fst: Seq_Nil{}, snd: Seq_Nil{}} 
    }
    Seq_Cons {head: h1, tail: Seq_Nil{}} => {
      {fst: Seq_Nil{}, snd: xs} 
    }
    Seq_Cons {head: h1, tail: Seq_Cons {head : h2, tail : tl2 }} => {
      let P = split_cn(tl2);
      {fst: Seq_Cons { head: h1, tail: P.fst},
       snd: Seq_Cons { head: h2, tail: P.snd}}
    }
  }
}
@*/


struct int_list_pair { 
  struct int_list* fst;
  struct int_list* snd;
};

// split [] = ([], []) 
// split [x] = ([], [x])
// split (x :: y :: zs) = let (xs, ys) = split(zs) in
//                        (x :: xs, y :: ys)
   


struct int_list_pair split(struct int_list *xs) 
/*@ requires is_null(xs) || !addr_eq(xs, NULL); @*/
/*@ requires take Xs = IntList(xs); @*/
/*@ ensures is_null(return.fst) || !addr_eq(return.fst, NULL); @*/
/*@ ensures is_null(return.snd) || !addr_eq(return.snd, NULL); @*/
/*@ ensures take Ys = IntList(return.fst); @*/
/*@ ensures take Zs = IntList(return.snd); @*/
{ 
  if (xs == 0) { 
    struct int_list_pair r = {.fst = 0, .snd = 0};
    return r;
  } else {
    if (xs->tail == 0) { 
      struct int_list_pair r = {.fst = 0, .snd = xs};
      return r;
    } else { 
      struct int_list *cdr = xs->tail;
      struct int_list_pair p = split(xs->tail->tail);
      xs->tail = p.fst;
      cdr->tail = p.snd;
      struct int_list_pair r = {.fst = xs, .snd = cdr};
      /*@ cn_print(r); @*/
      return r;
    }
  }
}

int main(void)
/*@ trusted; @*/
{
  struct int_list i1 = {.head = 2, .tail = 0};
  struct int_list i3 = {.head = 4, .tail = 0};
  struct int_list i2 = {.head = 3, .tail = &i3};

  struct int_list *il3 = IntList_append(&i1, &i2);
}
