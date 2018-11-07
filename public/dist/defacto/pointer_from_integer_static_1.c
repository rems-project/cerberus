#include <stdio.h>
#include <stdint.h>
#include "charon_concrete_addresses.h"
void f(uintptr_t i) {
  static int j=0;
  int *p = (int*)i;
  *p=1;
  printf("j=%d\n",j); 
}
int main() {
  uintptr_t j = ADDR007; // suppose this is the address of j
  f(j);
}
