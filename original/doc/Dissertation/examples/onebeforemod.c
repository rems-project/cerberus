int main(void) {
  int a[3];
  a[0] = 1;
  a[1] = 2;
  a[2] = 3;
  int *pa = &a[2];

  int sum = 0;
  while (pa > a) {
    sum = sum + *pa;
    pa = pa - 1;
  }
  return sum;
}
