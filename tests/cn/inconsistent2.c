void f (int *p) 
/*@ requires each(i32 i; 0i32 <= i && i <= 0i32) { i != 0i32 }; @*/
/*@ ensures false; @*/
{
  /*@ instantiate 0i32; @*/
}

int main(void)
/*@ trusted; @*/
{
  int p[5] = {1, 2, 3, 4, 5};
  f(p);
  return 0;
}

