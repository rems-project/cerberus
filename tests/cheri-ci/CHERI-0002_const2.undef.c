int aux(int *p)
{
  return p?(*p = 10):10;
}

int main(void)
{
  const int xxx = (aux((int*)&xxx), xxx); // the store in aux() is undefined
  aux((int*)&xxx); // the store in aux() is undefined
}