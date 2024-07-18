//CN_VIP #include <stdio.h>
//CN_VIP #include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <stddef.h>
#include "cn_lemmas.h"

int y=2, x=1;
int main()
/*CN_VIP*//*@ accesses x; accesses y; @*/
{
  int *p = &x+1;
  int *q = &y;
  uintptr_t i = (uintptr_t)p;
  uintptr_t j = (uintptr_t)q;
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
