
int
f (int *p, int *q)
/*@ requires q == array_shift(p, 10i32); @*/
{
  int x;
  x = p - q; // intentionally p - q = -10

  return x;
}

int main(void) {
  
  return 0;
}