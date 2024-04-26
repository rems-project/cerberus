

int
f (int *x)
/*@ requires take xv = Owned(x); @*/
/*@ requires 0i32 <= xv && xv < 500i32; @*/
/*@ ensures take xv2 = Owned(x); @*/
{
  return ((*x) + (*x));
}
