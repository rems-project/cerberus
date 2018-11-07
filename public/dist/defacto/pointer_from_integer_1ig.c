#include <stdio.h>
#include <stdint.h>
#include "charon_address_guesses.h"
void f(uintptr_t i) {
  int j=5;
  int *p = (int*)i;
  if (p==&j)
    *p=7;
  printf("j=%d &j=%p\n",j,(void*)&j); 
}
int main() {
  uintptr_t j = ADDRESS_PFI_1IG;
  f(j);
}
