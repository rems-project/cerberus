#include <stdio.h>

int main(void) {
  int a[] = {1,2,3};
  int *pa = &a[2];

  int sum = 0;
  while (pa > a) {
    sum += *pa;
    pa = pa - 1;
  }
  printf ("%d\n", sum);
  return 0;
}
