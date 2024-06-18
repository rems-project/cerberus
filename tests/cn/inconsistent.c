/*@  
predicate void False(pointer p, i32 i) {
  assert (i != 0i32);
  return;
}
@*/

void f (int *p) 
/*@ requires take f1 = each(i32 i; 0i32 <= i && i <= 0i32) { False(p + i, i) };
    ensures false; @*/
{
  /*@ extract False, 0i32; @*/
}

int main(void)
/*@ trusted; @*/
{
  int p[5] = {1, 2, 3, 4, 5};
  f(p);
  return 0;
}
