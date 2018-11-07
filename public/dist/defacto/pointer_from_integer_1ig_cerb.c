#include <stdio.h>
#include <stdint.h>
void f(uintptr_t i) {
  int j=0;
  int *p = (int*)i;
  if (p==&j)
    *p=1;
  printf("j=%d\n",j);
}
int main() {
  uintptr_t j = 0x20;
  f(j);
}
