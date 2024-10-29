#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <inttypes.h>
int main() {
  int x=1, y=2;
  int *p = &x;
  int *q = &y;
  uintptr_t i = (uintptr_t) p;
  uintptr_t j = (uintptr_t) q;
  uintptr_t k = i ^ j;
  uintptr_t l = k ^ i;
#if defined(ANNOT)
  int *r = copy_alloc_id(l, q);
#else
  int *r = (int *)l; // VIP roundtrip provenance is not preserved via operations
#endif
  // are r and q now equivalent?
  *r = 11;     // CN VIP UB (no annot)
  _Bool b = (r==q);
  //CN_VIP printf("x=%i y=%i *r=%i (r==p)=%s\n",x,y,*r, b?"true":"false");
  /*CN_VIP*//*@ assert(x == 1i32 && y == 11i32 && *r == 11i32 && b == 1u8); @*/
}
