//CN_VIP #include <stdio.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int y=2, x=1;
int main() {
  /*@ apply assert_equal((u64)&x + 4u64, (u64)&y); @*/
  uintptr_t p = (uintptr_t)(&x + 1);
  uintptr_t q = (uintptr_t)&y;
  //CN_VIP printf("Addresses: p=%" PRIxPTR " q=%" PRIxPTR "\n", (unsigned long)p,(unsigned long)q);
  _Bool b = (p==q);
  // can this be false even with identical addresses?
  //CN_VIP printf("(p==q) = %s\n", b?"true":"false");
  /*CN_VIP*//*@ assert (b == 1u8); @*/
  return 0;
}

// The evaluation table in the appendix of the VIP paper is misleading.
// This file has UB under PNVI-ae-udi without annotations because
// of allocation address non-determinism (demonic)
// The desired behaviour can be obtained by asserting the addresses are adjacent.
