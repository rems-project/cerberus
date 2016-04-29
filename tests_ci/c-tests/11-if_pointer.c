int main(void)
{
  int x;
  int *p = &x;
  if (p)
    return 10;
  else
    return 20;
}
