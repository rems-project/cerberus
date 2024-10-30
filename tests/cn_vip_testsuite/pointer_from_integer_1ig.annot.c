#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <stdint.h>
#include "charon_address_guesses.h"
#include "cn_lemmas.h"
void f(uintptr_t i) {
  int j=5;
  /*CN_VIP*//*@ apply assert_equal(i, (u64)&j); @*/
#if defined(ANNOT)
  int *p = copy_alloc_id(i, &j);
#else
  int *p = (int*)i; // not even round-trip can save this
#endif
  if (p==&j) {
    *p=7; // CN VIP UB (no annot)
    /*CN_VIP*//*@ assert (j == 7i32); @*/
  }
  //CN_VIP printf("j=%d &j=%p\n",j,(void*)&j);
}
int main() {
  uintptr_t j = ADDRESS_PFI_1IG;
  f(j);
}
