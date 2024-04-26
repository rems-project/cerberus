

struct two_ints {
  int x;
  int y;
};

/* FIXME: better syntax for else-if, and for checking a pointer
   is correctly aligned to point at a particular type */

/*@
predicate {i32 k} Tagged_Pointer (pointer p, i32 k) {
  if (k == 0i32) {
    return {k: k};
  }
  else { if (k == 1i32) {
    assert (mod((u64)p, ((u64) (sizeof<int>))) == 0u64);
    take V = Owned<int>(p);
    return {k: k};
  }
  else {
    assert (k == 2i32);
    assert (mod((u64)p, ((u64) (sizeof<struct two_ints>))) == 0u64);
    take V = Owned<struct two_ints>(p);
    return {k: k};
  } }
}
@*/

int
f (void *p, int k)
/*@ requires take X = Tagged_Pointer (p, k); @*/
/*@ ensures take X2 = Tagged_Pointer (p, k); @*/
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


