#include <stdio.h>
#include <stdint.h>
#include "charon_address_guesses.h"
void f(int *p) {
  int j=5;
  *p=7;
  printf("j=%d\n",j); 
}
int main() {
  uintptr_t i = ADDRESS_PFI_1P;
  int *p = (int*)i;
  f(p);
}
