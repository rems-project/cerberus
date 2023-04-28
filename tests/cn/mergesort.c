struct int_list { 
  int head;
  struct int_list* tail;
};

datatype seq { 
  Seq_Nil {},
  Seq_Cons {integer head, datatype seq tail}
}

predicate (datatype seq) IntList(pointer p) {
  if (p == NULL) { 
    return Seq_Nil{};
  } else { 
    take H = Owned<struct int_list>(p);
    take tl = IntList(H.tail);
    return (Seq_Cons { head: H.head, tail: tl });
  }
}

function [rec] ({datatype seq fst, datatype seq snd}) split(datatype seq xs) 
{
  return (match xs {
    Seq_Nil {} => { 
      {fst: Seq_Nil{}, snd: Seq_Nil{}} 
    }
    Seq_Cons {head: h1, tail: Seq_Nil{}} => {
      {fst: Seq_Nil{}, snd: xs} 
    }
    Seq_Cons {head: h1, tail: Seq_Cons {head : h2, tail : tl2 }} => {
      let P = split(tl2);
      {fst: Seq_Cons { head: h1, tail: P.fst},
       snd: Seq_Cons { head: h2, tail: P.snd}}
    }
    });
}

function [rec] (datatype seq) merge(datatype seq xs, datatype seq ys) { 
  return (match xs { 
      Seq_Nil {} => { ys }
      Seq_Cons {head: x, tail: xs1} => {
	match ys {
	  Seq_Nil {} => { xs }
	  Seq_Cons{ head: y, tail: ys1} => {
	    let tail = merge(xs1, ys1);
	    (x < y) ?
	    (Seq_Cons{ head: x, tail: Seq_Cons {head: y, tail: tail}})
	    : (Seq_Cons{ head: y, tail: Seq_Cons {head: x, tail: tail}})
	  }
	}
      }
    });
}

function [rec] (datatype seq) mergesort(datatype seq xs) { 
  return (match xs {
      Seq_Nil{} => { xs }
      Seq_Cons{head: x, tail: Seq_Nil{}} => { xs }
      Seq_Cons{head: x, tail: Seq_Cons{head: y, tail: zs}} => {
	let P = split(xs);
	let L1 = mergesort(P.fst);
	let L2 = mergesort(P.snd);
	merge(L1, L2)
      }
    });
}
	    

struct int_list_pair { 
  struct int_list* fst;
  struct int_list* snd;
};

   


struct int_list_pair split(struct int_list *xs) 
/*@ requires take Xs = IntList(xs) @*/
/*@ ensures take Ys = IntList(return.fst) @*/
/*@ ensures take Zs = IntList(return.snd) @*/
{ 
  if (xs == 0) { 
    struct int_list_pair r = {.fst = 0, .snd = 0};
    return r;
  } else {
    /*@ unpack IntList(xs); @*/
    if (xs->tail == 0) { 
      struct int_list_pair r = {.fst = 0, .snd = xs};
      return r;
    } else { 
      struct int_list *cdr = xs->tail;
      struct int_list_pair p = split(xs->tail->tail);
      xs->tail = p.fst;
      cdr->tail = p.snd;
      struct int_list_pair r = {.fst = xs, .snd = cdr};
      return r;
    }
  }
}

