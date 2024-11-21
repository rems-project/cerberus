#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <stdint.h>
#include "charon_address_guesses.h"
#include "cn_lemmas.h"
void f(uintptr_t i) {
  int j=5;
  /*@ apply assert_equal(i, (u64)&j); @*/
#if defined(ANNOT)
  int *p = copy_alloc_id(i, &j);
#else
  int *p = (int*)i;
#endif
  *p=7;
  //CN_VIP printf("j=%d\n",j);
  /*CN_VIP*//*@ assert (j == 7i32); @*/
}
int main() {
  uintptr_t j = ADDRESS_PFI_1I;
  f(j);
}
