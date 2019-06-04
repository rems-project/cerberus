int main()
{
  int *p;
  int x = 0;
  if (p == &x)
   *p = 1;
  return x;
}