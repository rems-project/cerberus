#include <stdio.h>
#include <stdint.h>
#include "charon_address_guesses.h"
void f(uintptr_t i) {
  int j=5; 
  int *p = (int*)i;
  __BMC_ASSUME ((intptr_t)p == ADDRESS_PFI_1I);
  *p=7;
  printf("j=%d\n",j); 
}
int main() {
  uintptr_t j = ADDRESS_PFI_1I;
  f(j);
}
