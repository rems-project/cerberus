#include <stdio.h>
#include <inttypes.h>
int main() {
  int a[2];
  int *p = &a[0];
  uintptr_t i = (uintptr_t)p;
  uintptr_t j = i + sizeof (int);
  int *q = (int *)j;    // defined behaviour?
  *q=11;                // defined behaviour?
  printf("a[1]=%d\n",a[1]);
}

