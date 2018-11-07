#include <stdio.h>
#include <stdint.h>
void f(int *p) {
  int j=0;
  if (p==&j)
    *p=1;
  printf("j=%d\n",j);
}
int main() {
  uintptr_t i = 0x28;
  int *p = (int*)i;
  f(p);
}
