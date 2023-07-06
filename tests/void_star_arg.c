

struct two_ints {
  int x;
  int y;
};

/* FIXME: better syntax for else-if, and for checking a pointer
   is correctly aligned to point at a particular type */

/*@
predicate {integer k} Tagged_Pointer (pointer p, integer k) {
  if (k == 0) {
    return {k: k};
  }
  else { if (k == 1) {
    assert (mod((integer)p, 4) == 0);
    take V = Owned<int>(p);
    return {k: k};
  }
  else {
    assert (k == 2);
    assert (mod((integer)p, 8) == 0);
    take V = Owned<struct two_ints>(p);
    return {k: k};
  } }
}
@*/

int
f (void *p, int k)
/*@ requires take X = Tagged_Pointer (p, k) @*/
/*@ ensures take X2 = Tagged_Pointer (p, k) @*/
{
  int *p2;
  struct two_ints *p3;
  if (k == 0) {
    return 0;
  }
  else if (k == 1) {
    p2 = p;
    return *p2;
  }
  else if (k == 2) {
    p3 = p;
    return (p3->x < p3->y) ? 1 : 0;
  }
  else {
    /*@ assert (false); @*/
  }
}


