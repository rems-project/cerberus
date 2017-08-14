const int* f(void)
{
  return 0;
}

int main(void)
{
  *f() = 10; // shouldn't typecheck
}
