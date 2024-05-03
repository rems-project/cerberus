#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <stdint.h>
#include "charon_address_guesses.h"
void f(uintptr_t i) {
  int j=5;
#if defined(ANNOT)
  int *p = copy_alloc_id(i, &j);
#else
  int *p = (int*)i;
#endif
  if (p==&j)
    *p=7;
  //CN_VIP printf("j=%d &j=%p\n",j,(void*)&j);
}
int main() {
  uintptr_t j = ADDRESS_PFI_1IG;
  f(j);
}
