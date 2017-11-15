int main(void) {
  long a = 1L;
  int *pa = (int *) &a;
  pa = pa + 1;
  return *pa;
}
