int f(int x) 
/*@ ensures return == ((0i32 <= x && x <= 30i32) ? 1i32 : 0i32); @*/
{
  switch (x) {
    case 0 ... 30:
      return 1;
    default:
      return 0;    
  }
}

int main(void)
{
  int r = f(29);
}
