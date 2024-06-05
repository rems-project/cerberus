#define ite(x,y,z)  __builtin_choose_expr(x,y,z)


int f () 
/*@ ensures return == 20i32; @*/
{
  return ite(1,20,30);
}


int g () 
/*@ ensures return == 30i32; @*/
{
  return ite(0,20,30);
}

int main(void) {
  int r1 = f();
  int r2 = g();
  return 0;
}
