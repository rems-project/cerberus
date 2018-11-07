#include <stdio.h>
#include <stdint.h>
#include "charon_concrete_addresses.h"
void f(uintptr_t i) {
  int *p = (int*) i;
  *p=1;
}
int main() {
  static int j=0;
  f(ADDR014); // suppose this is the address of j
  printf("j=%d\n",j); 
}
