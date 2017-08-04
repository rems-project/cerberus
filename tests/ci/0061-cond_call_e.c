int f(void)
{
  return 10;
}
int g(void)
{
  return 20;
}

int main(void)
{
  int x = 1;
  return (x?f:g)();
}
