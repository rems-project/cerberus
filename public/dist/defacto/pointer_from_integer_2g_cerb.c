#include <stdio.h>
#include <stdint.h>
void f() {
  uintptr_t i=0x10;
  int *p = (int*)i;
  *p=1;
}
int main() {
  int j=0;
  if ((uintptr_t)&j == 0x10)
    f();
  printf("j=%d\n",j); 
}
