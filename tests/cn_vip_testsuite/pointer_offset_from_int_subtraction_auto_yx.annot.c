#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int main() {
  int y=2, x=1;
  uintptr_t ux = (uintptr_t)&x;
  uintptr_t uy = (uintptr_t)&y;
  uintptr_t offset = uy - ux;
  //CN_VIP printf("Addresses: &x=%"PRIuPTR" &y=%"PRIuPTR\
         " offset=%"PRIuPTR" \n",(unsigned long)ux,(unsigned long)uy,(unsigned long)offset);
#if defined(ANNOT)
  int *p = copy_alloc_id(ux + offset, &y);
#else
  int *p = (int *)(ux + offset);
#endif
  int *q = &y;
  /*CN_VIP*/if (&p == &q) return 0;                                         // CN used to derive disjointness and non-null
  /*CN_VIP*/if ((uintptr_t)&p + sizeof(int*) < (uintptr_t)&p) return 0;     // constraints from resource ownership, but this
  /*CN_VIP*/if ((uintptr_t)&q + sizeof(int*) < (uintptr_t)&q) return 0;     // was removed for performance reasons.
  /*CN_VIP*/unsigned char *p_bytes = owned_int_ptr_to_owned_uchar_arr(&p);
  /*CN_VIP*/unsigned char *q_bytes = owned_int_ptr_to_owned_uchar_arr(&q);
  int result = _memcmp(p_bytes, q_bytes, sizeof(p));
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(p_bytes); @*/
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(q_bytes); @*/
  if (result == 0) {
    *p = 11; // is this free of UB?
    //CN_VIP printf("x=%d y=%d *p=%d *q=%d\n",x,y,*p,*q);
    /*CN_VIP*/ /*@ assert(x == 1i32 && y == 11i32 && *p == 11i32 && *q == 11i32); @*/
  }
}
