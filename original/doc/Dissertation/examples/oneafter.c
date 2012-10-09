int main(void) {
  int a[3];
  a[0] = 1;
  a[1] = 2;
  a[2] = 3;
  int *pa = &a;

  int sum = 0;
  while (&a[3] > pa) {
    sum = sum + *pa;
    pa = pa + 1;
  }
  return sum;
}
