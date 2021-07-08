#include "refinedc.h"

#include <stdio.h>
#include <stdint.h>
#include "charon_address_guesses.h"
void f(uintptr_t i) {
  int j=5; 
#if defined(ANNOT)
  int *p = copy_alloc_id(i, &j);
#else
  int *p = (int*)i;
#endif
  *p=7;
  printf("j=%d\n",j); 
}
int main() {
  uintptr_t j = ADDRESS_PFI_1I;
  f(j);
}
