#include <stdio.h>
#include <stdint.h>
#include "charon_concrete_addresses.h"
void f(uintptr_t i) {
  static int j=0;
  int *p = (int*)i;
  uintptr_t jp = (uintptr_t)&j;
  if (i == jp) 
    *p=1;
  printf("j=%d\n",j); 
}
int main() {
  f(ADDR013); // suppose this is the address of j
}
