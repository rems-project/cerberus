#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <stdint.h>
#include "charon_address_guesses.h"
#include "cn_lemmas.h"
void f(uintptr_t i) {
  int j=5;
  uintptr_t k = (uintptr_t)&j;
  /*CN_VIP*//*@ apply assert_equal(i, k); @*/
#if defined(ANNOT)
  int *p = copy_alloc_id(i, &j);
#else
  int *p = (int*)i;
#endif
  *p=7;
  /*CN_VIP*//*@ assert (j == 7i32); @*/
  //CN_VIP printf("j=%d\n",j);
}
int main() {
  uintptr_t j = ADDRESS_PFI_1I;
  f(j);
}

// The evaluation table in the appendix of the VIP paper is misleading.
// This file has UB under PNVI-ae-udi without annotations because
// of allocation address non-determinism (demonic)
// The desired behaviour can be obtained by asserting the addresses are equal.
