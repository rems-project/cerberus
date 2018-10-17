#include <stdio.h>
int main() {
  int a[2][2] = {{1,2},{3,4}};
  int *p00 = &(a[0][0]);
  int *p11 = &(a[1][1]);
  int sum = 0;
  for (int *p = p00; p <= p11; ++p) // defined behaviour?
    sum = sum + *p;                 // defined behaviour?
  printf("sum=%d\n",sum);
}
