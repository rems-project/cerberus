#include <stdio.h>
#include <stdint.h>
#include "charon_address_guesses.h"
void f() {
  uintptr_t i=ADDRESS_PFI_2G;
  int *p = (int*)i;
  *p=7;
}
int main() {
  int j=5;
  __BMC_ASSUME((uintptr_t)&j == ADDRESS_PFI_2G);
  if ((uintptr_t)&j == ADDRESS_PFI_2G)
    f();
  printf("j=%d &j=%p\n",j,(void*)&j); 
}
