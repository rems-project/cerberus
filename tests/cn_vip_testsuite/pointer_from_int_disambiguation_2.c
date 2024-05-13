//CN_VIP #include <stdio.h>
//CN_VIP #include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <stddef.h>
#include "cn_lemmas.h"

int y=2, x=1;
int main() {
  int *p = &x+1;
  int *q = &y;
  uintptr_t i = (uintptr_t)p;
  uintptr_t j = (uintptr_t)q;
  /*CN_VIP*/if (&p == &q) return 0;                                         // CN used to derive disjointness and non-null
  /*CN_VIP*/if ((uintptr_t)&p + sizeof(int*) < (uintptr_t)&p) return 0;     // constraints from resource ownership, but this
  /*CN_VIP*/if ((uintptr_t)&q + sizeof(int*) < (uintptr_t)&q) return 0;     // was removed for performance reasons.
  /*CN_VIP*/ unsigned char *p_bytes = owned_int_ptr_to_owned_uchar_arr(&p);
  /*CN_VIP*/ unsigned char *q_bytes = owned_int_ptr_to_owned_uchar_arr(&q);
  if (_memcmp(p_bytes, q_bytes, sizeof(p)) == 0) {
    int *r = (int *)i;
    r=r-1;  // is this free of UB?
    *r=11;  // and this?
    //CN_VIP printf("x=%d y=%d *q=%d *r=%d\n",x,y,*q,*r);
    /*CN_VIP*//*@ assert (x == 11i32 && y == 2i32 && *q == 2i32 && *r == 11i32); @*/
  }
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(p_bytes); @*/
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(q_bytes); @*/
}
