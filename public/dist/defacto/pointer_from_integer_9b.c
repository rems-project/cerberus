#include <stdio.h>
#include <stdint.h>
#include "charon_concrete_addresses.h"
void f(uintptr_t i) {
  static int j=0;
  int *q = &j;
  int *p = (int*)i;
  if (p==&j) 
    *p=1;
  printf("j=%d\n",j); 
}
int main() {
  uintptr_t j = ADDR016; // suppose this is the address of j
  f(j);
}

