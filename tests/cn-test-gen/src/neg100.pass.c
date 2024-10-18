int negative100(int x)
/*@ requires x == 100i32;
    ensures return == -100i32;
@*/
{
  return -x;
}
