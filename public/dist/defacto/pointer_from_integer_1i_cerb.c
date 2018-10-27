#include <stdio.h>
#include <stdint.h>
void f(uintptr_t i) {
  int j=0;
  int *p = (int*)i;
  *p=1;
  printf("j=%d\n",j); 
}
int main() {
  uintptr_t j = 32; // 0x7fffffffdd7cULL;
  f(j);
}
