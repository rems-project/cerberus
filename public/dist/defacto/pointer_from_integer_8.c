#include <stdio.h>
#include <stdint.h>
void f(uintptr_t xi) {
  int j = 0;
  int *p = (int*)xi;
  *p = 1;
  printf("j=%d\n",j);
  //printf("p=%p  &j=%p\n",(void*)p,(void*)&j);
}
int main() {
  int k = 0;
  uintptr_t xk = (uintptr_t)&k;
  uintptr_t xj = xk - 0x28; // for GCC O0
  //uintptr_t xj = xk - 0x18; // for GCC O0
  //uintptr_t xj = xk - 0x20;   // for GCC O2
  f(xj);
}
