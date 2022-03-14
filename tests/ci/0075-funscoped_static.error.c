int f(int n)
{
  static int acc = 0;
  
  if (!n)
    return acc;
  
  acc += n--;
  return f(n);
}

int main(void)
{
  return y; //f(4); // should return 10
}
