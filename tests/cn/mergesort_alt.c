struct node {
  int value;
  struct node *next;
};

typedef struct node * ilist;

/*@
datatype list {
  Nil {},
  Cons {i32 head, list tail}
}

predicate (list) List(pointer p) {
  if (is_null(p)) {
    return Nil {};
  } else {
    take node = Owned<struct node>(p);
    take tl = List(node.next);
    return (Cons { head: node.value, tail: tl });
  }
}

predicate (list) ListP(pointer p) {
  take l = Owned<struct node *>(p);
  take xs = List(l);
  return xs;
}
@*/

/*@
function [rec] ({list fst, list snd}) cn_split(list xs) {
  match xs {
    Nil {} => {
      {fst: Nil {}, snd: Nil {}}
    }
    Cons {head: h1, tail: Nil {}} => {
      {fst: xs, snd: Nil {}}
    }
    Cons {head: h1, tail: Cons {head : h2, tail : tl2 }} => {
      let P = cn_split(tl2);
      {fst: Cons { head: h1, tail: P.fst},
       snd: Cons { head: h2, tail: P.snd}}
    }
  }
}

function [rec] (list) cn_merge(list xs, list ys) {
  match xs {
    Nil {} => {
      ys
    }
    Cons {head: x, tail: xs_} => {
      match ys {
        Nil {} => {
          xs
        }
        Cons {head: y, tail: ys_} => {
          if (x <= y) {
            Cons {head: x, tail: cn_merge(xs_, ys)}
          } else {
            Cons {head: y, tail: cn_merge(xs, ys_)}
          }
        }
      }
    }
  }
}

function [rec] (list) cn_mergesort(list xs) {
  match xs {
    Nil {} => { 
      xs 
    }
    Cons {head: x, tail: Nil {}} => { 
      xs 
    }
    Cons {head: x, tail: Cons {head: y, tail: zs}} => {
      let P = cn_split(xs);
      let L1 = cn_mergesort(P.fst);
      let L2 = cn_mergesort(P.snd);
      cn_merge(L1, L2)
    }
  }
}

function (boolean) smaller (i32 head, list xs) {
  match xs {
    Nil {} => {
      true
    }
    Cons {head : x, tail : _} => {
      head <= x
    }
  }
}

function [rec] (boolean) is_sorted(list xs) {
  match xs {
    Nil {} => { 
      true 
    }
    Cons {head: head, tail: tail} => { 
      smaller (head, tail) && is_sorted(tail)
    }
  }
}

function (list) tl (list xs) {
  match xs {
    Nil {} => {
      Nil {}
    }
    Cons {head : _, tail : tail} => {
      tail
    }
  }
}
@*/

ilist split(ilist xs)
/*@ requires take Xs = List(xs);
    ensures take Ys = List(xs);
            take Zs = List(return);
            {fst: Ys, snd: Zs} == cn_split(Xs);
@*/
{
  /*@ unfold cn_split(Xs); @*/
  if (xs == 0 || xs->next == 0) {
    return 0;
  } else {
    struct node *cdr = xs->next;
    ilist ys = split(cdr->next);
    xs->next = cdr->next;
    cdr->next = ys;
    return cdr;
  }
}


void prove_merge_sorted(struct node *p, struct node *q)
/*@ requires take xs_in = List(p);
             take ys_in = List(q);
             is_sorted(xs_in);
             is_sorted(ys_in);
             let merged = cn_merge(xs_in, ys_in);
    ensures  take xs_out = List(p);
             take ys_out = List(q);
             xs_out == xs_in && ys_out == ys_in;
             is_sorted(merged);
@*/
{
  /* Unfold the definition of `merged`. */
  /*@ unfold cn_merge(xs_in, ys_in); @*/

  /* If either list is empty, cn_merge just picks the other, which is
     sorted by assumption, so nothing left to do. */
  if (p == 0 || q == 0) {
    return;
  } 
  /* For non-empty lists, cn_merge picks the smaller head and merges
     the rest. */
  else {
    /* If `xs_in` has the smaller head, it merges `tl(xs_in)` with
       `ys_in`. */
    if (p->value <= q->value) {
      /* By induction hypothesis (IH) `cn_merge(tl(xs_in), ys_in))` is
         sorted. To "apply" IH, expand the definition of
         `is_sorted(xs_in)` to prove `is_sorted(tl(xs_in))`. */
      /*@ unfold is_sorted(xs_in); @*/
      prove_merge_sorted(p->next, q);
      /* By definition of `cn_merge(tl(xs_in), ys_in)`, that merged
         list starts with the minimum of either head, ... */
      /*@ unfold cn_merge(tl(xs_in), ys_in); @*/
      /* ... so that list with `hd(xs_in)` cons'ed on is also
         sorted. @*/
      /*@ unfold is_sorted(merged); @*/
      return;
    }
    else {
      /* This is symmetric to the proof above. */
      /*@ unfold is_sorted(ys_in); @*/
      prove_merge_sorted(p, q->next);
      /*@ unfold cn_merge(xs_in, tl(ys_in)); @*/
      /*@ unfold is_sorted(merged); @*/
      return;
    }
  }
}


struct node *merge(struct node *xs, struct node *ys)
/*@ requires take Xs = List(xs);
             take Ys = List(ys);
    ensures take Zs = List(return);
            Zs == cn_merge(Xs, Ys); @*/
{
  /*@ unfold cn_merge(Xs, Ys); @*/
  if (xs == 0) {
    return ys;
  } else if (ys == 0) {
    return xs;
  } else if (xs->value <= ys->value) {
    xs->next = merge(xs->next, ys);
    return xs;
  } else {
    ys->next = merge(xs, ys->next);
    return ys;
  }
}

void naive_mergesort(ilist *p)
/*@ requires take xs_in = ListP(p);
             let sorted = cn_mergesort(xs_in);
    ensures take xs_out = ListP(p);
            xs_out == sorted; 
            is_sorted(xs_out);
@*/
{
  /*@ unfold cn_mergesort(xs_in); @*/
  /*@ unfold is_sorted(sorted); @*/
  /*@ unfold is_sorted(tl(sorted)); @*/
  ilist xs = *p;
  if (xs != 0 && xs->next != 0) {
    ilist ys = split(xs);
    naive_mergesort(&xs);
    naive_mergesort(&ys);
    /*CN*/ prove_merge_sorted(xs, ys);
    *p = merge(xs, ys);
    return;
  }
}




int main(void)
/*@ trusted; @*/
{
  ilist xs;
  struct node n1;
  struct node n2;
  struct node n3;

  n1.value = 1;
  n2.value = 4;
  n3.value = 3;

  xs = &n1;
  n1.next = &n2;
  n2.next = &n3;
  n3.next = 0;

  naive_mergesort(&xs);
}







