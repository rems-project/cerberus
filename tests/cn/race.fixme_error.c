

int
f (int *x)
/*@ requires take xv = Owned(x) @*/
/*@ requires 0 <= xv && xv < 500 @*/
/*@ ensures take xv2 = Owned(x) @*/
{
  return ((*x) + (*x));
}
