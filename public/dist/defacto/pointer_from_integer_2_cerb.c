#include <stdio.h>
#include <stdint.h>
void f() {
  uintptr_t i = 16; // 0x7fffffffdd8cULL
  int *p = (int*)i;
  *p=1;
}
int main() {
  int j=0;
  f();
  printf("j=%d\n",j);
  return (uintptr_t)&j;
}
