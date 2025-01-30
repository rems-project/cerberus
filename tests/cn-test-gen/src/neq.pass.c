int ret_17_except_good(int x)
/*@ requires x != 10i32;
    ensures return == 17i32; @*/
{
  if (x == 10) {
    return 23;
  } else {
    return 17;
  }
}
