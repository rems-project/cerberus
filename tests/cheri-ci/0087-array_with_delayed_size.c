int main(void)
{
  // during the initialisation of y, the type of x should already be int[3]
  int x[] = {1,2,3}, y = sizeof(x);
  return y; // SHOULD RETURN ivsizeof(int[3])
}
