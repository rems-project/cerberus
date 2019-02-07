#include <stdio.h>
#include <stdint.h>
#include "charon_address_guesses.h"
void f() {
  uintptr_t i=ADDRESS_PFI_2;
  int *p = (int*)i;
  *p=7;
}
int main() {
  int j=5;
  __BMC_ASSUME((uintptr_t)&j == ADDRESS_PFI_2);
  f();
  printf("j=%d\n",j); 
}
