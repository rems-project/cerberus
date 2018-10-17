#include <stdio.h>
int main() {
  int a[2][2] = {{1,2},{3,4}};
  int *p00 = &(a[0][0]);
  int *p11 = p00 + 1*2 + 1; // defined behaviour?
  *p11 = 44;
  printf("a[1][1]=%d\n",a[1][1]);
}

