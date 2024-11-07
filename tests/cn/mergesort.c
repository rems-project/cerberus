struct node {
  int value;
  struct node* next;
};

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

function [rec] ({list fst, list snd}) cn_split(list xs) {
  match xs {
    Nil {} => {
      {fst: Nil {}, snd: Nil {}}
    }
    Cons {head: h1, tail: Nil {}} => {
      {fst: Nil {}, snd: xs}
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
      Cons {head: x, tail: xs1} => {
	match ys {
	  Nil {} => { 
            xs 
          }
	  Cons { head: y, tail: ys1} => {
	    let tail = cn_merge(xs1, ys1);
	    (x < y) ?
	    (Cons { head: x, tail: Cons {head: y, tail: tail}})
	    : (Cons { head: y, tail: Cons {head: x, tail: tail}})
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
@*/

struct node_pair {
  struct node* fst;
  struct node* snd;
};

struct node_pair split(struct node *xs)
/*@ requires take Xs = List(xs); @*/
/*@ ensures take Ys = List(return.fst); @*/
/*@ ensures take Zs = List(return.snd); @*/
/*@ ensures {fst: Ys, snd: Zs} == cn_split(Xs); @*/
{
  /*@ unfold cn_split(Xs); @*/
  if (xs == 0) {
    struct node_pair r = {.fst = 0, .snd = 0};
    return r;
  } else {
    struct node *cdr = xs->next;
    if (cdr == 0) {
      struct node_pair r = {.fst = 0, .snd = xs};
      return r;
    } else {
      struct node_pair p = split(cdr->next);
      xs->next = p.fst;
      cdr->next = p.snd;
      struct node_pair r = {.fst = xs, .snd = cdr};
      return r;
    }
  }
}

struct node* merge(struct node *xs, struct node *ys)
/*@ requires take Xs = List(xs); @*/
/*@ requires take Ys = List(ys); @*/
/*@ ensures take Zs = List(return); @*/
/*@ ensures Zs == cn_merge(Xs, Ys); @*/
{
  /*@ unfold cn_merge(Xs, Ys); @*/
  if (xs == 0) {
    return ys;
  } else {
    if (ys == 0) {
      return xs;
    } else {
      struct node *zs = merge(xs->next, ys->next);
      if (xs->value < ys->value) {
	xs->next = ys;
	ys->next = zs;
	return xs;
      } else {
	ys->next = xs;
	xs->next = zs;
	return ys;
      }
    }
  }
}

struct node* naive_mergesort(struct node *xs)
/*@ requires take Xs = List(xs); @*/
/*@ ensures take Ys = List(return); @*/
/*@ ensures Ys == cn_mergesort(Xs); @*/
{
  /*@ unfold cn_mergesort(Xs); @*/
  if (xs == 0) {
    return xs;
  } else if (xs->next == 0) {
    return xs;
  } else {
    struct node_pair p = split(xs);
    p.fst = naive_mergesort(p.fst);
    p.snd = naive_mergesort(p.snd);
    return merge(p.fst, p.snd);
  }
}

int main(void)
/*@ trusted; @*/
{
  struct node i3 = {.value = 3, .next = 0};
  struct node i2 = {.value = 4, .next = &i3};
  struct node i1 = {.value = 2, .next = &i2};

  struct node *sorted_i1 = naive_mergesort(&i1);
}
