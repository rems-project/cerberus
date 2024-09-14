int main(void)
{
  const int xxx = 42;
  int *p = (int*)&xxx;
  xxx;
  *p = 100; // undefined
}