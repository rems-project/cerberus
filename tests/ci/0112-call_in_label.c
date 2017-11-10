void f(void)
{
  
}

int main(void)
{
  int x = 0;
 l:
  if (x)
    return 0;
  f();
  x = 1;
  goto l;
}
