
/* A test case about modulus and masking, in both integers and pointers.
   Originally introduced as a test case because the pointer variant was causing
   issues for the SMT solver for unclear reasons.
*/

typedef unsigned long long u64;

enum {
  SHIFT_AMOUNT = 5
};

u64
foo_integer (u64 y)
/*@ requires mod(y, shift_left(1u64, ((u64) SHIFT_AMOUNT))) == 0u64 @*/
{
  u64 x = y;
  x &= ~ ((1UL << SHIFT_AMOUNT) - 1);
  /*@ assert (x == y); @*/
  return x;
}



int *
foo (int *p)
/*@ requires let p_u64 = (u64) p @*/
/*@ requires mod(p_u64, shift_left(1u64, ((u64) SHIFT_AMOUNT))) == 0u64 @*/
{
  u64 x = ((u64) p);
  int *p2;

  x &= ~ ((1UL << SHIFT_AMOUNT) - 1);

  p2 = ((int *) x);
  /*@ assert (((u64) p2) == ((u64) p)); @*/
  return p2;
}


