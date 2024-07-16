//CN_VIP #include <stdio.h>
#include <string.h>
#include <stddef.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int y=2, x=1;
int main()
/*CN_VIP*//*@ accesses y; @*/
{
  int *p = &x;
  int *q = &y;
  ptrdiff_t offset = q - p;
  int *r = p + offset;
  /*CN_VIP*/if (&r == &q) return 0;                                         // CN used to derive disjointness and non-null
  /*CN_VIP*/if ((uintptr_t)&r + sizeof(uintptr_t) < (uintptr_t)&r) return 0;// constraints from resource ownership, but this
  /*CN_VIP*/if ((uintptr_t)&q + sizeof(uintptr_t) < (uintptr_t)&q) return 0;// was removed for performance reasons.
  /*CN_VIP*/unsigned char* r_bytes = owned_int_ptr_to_owned_uchar_arr(&r);
  /*CN_VIP*/unsigned char* q_bytes = owned_int_ptr_to_owned_uchar_arr(&q);
  /*CN_VIP*/int result = _memcmp(r_bytes, q_bytes, sizeof(r));
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(r_bytes); @*/
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(q_bytes); @*/
  if (result == 0) {
    *r = 11; // is this free of UB?
    //CN_VIP printf("y=%d *q=%d *r=%d\n",y,*q,*r);
  }
}
