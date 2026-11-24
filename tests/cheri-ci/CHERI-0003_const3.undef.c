int aux(int *p)
{
  return p?(*p = 10):10;
}

int main(void)
{
  const int xxx = (aux(0), xxx);
  aux((int*)&xxx); // the store in aux() is undefined
}