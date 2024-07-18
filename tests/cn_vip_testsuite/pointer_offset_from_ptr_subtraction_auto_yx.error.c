//CN_VIP #include <stdio.h>
#include <string.h>
#include <stddef.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int main() {
  int y=2, x=1;
  int *p = &x;
  int *q = &y;
  ptrdiff_t offset = q - p;
  int *r = p + offset;
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
