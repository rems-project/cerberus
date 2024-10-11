int abs_mem(int* p)
/*@ requires take x = Owned<int>(p);
             MINi32() < x;
    ensures take x2 = Owned<int>(p);
            x == x2;
            return == ((x >= 0i32) ? x : (0i32-x));
@*/
{
  int x = *p;
  if (x >= 0) {
    return x;
  }
  else {
    return x;
  }
}