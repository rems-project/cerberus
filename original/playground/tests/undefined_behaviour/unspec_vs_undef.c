#include "stdio.h"

int x = 0;

int f() {
  x++;
  return x;
}

int g() {
  return x;
}

int main() {
  int t;
  int *p;
  int a[] = {1,2,3};
  t = g() + f();
  p = a + t;
  printf("%d\n", a[1] + (*p = 5, 0));
  return 0;
}
