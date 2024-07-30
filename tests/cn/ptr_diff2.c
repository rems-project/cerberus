int* f(int *p)
/*@ ensures ptr_eq(return, array_shift(p, -1i32)); @*/
{
  return p - 1;
}

int main(void)
{
    int arr = 0;
    f(&arr + 1); 
}
