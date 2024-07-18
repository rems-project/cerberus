//CN_VIP #include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int y=2, x=1;
int main()
/*CN_VIP*//*@ accesses y; @*/
{
  int *p = &x + 1;
  int *q = &y;
  //CN_VIP printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  /*CN_VIP*/unsigned char* p_bytes = owned_int_ptr_to_owned_uchar_arr(&p);
  /*CN_VIP*/unsigned char* q_bytes = owned_int_ptr_to_owned_uchar_arr(&q);
  /*CN_VIP*/int result = _memcmp(p_bytes, q_bytes, sizeof(p));
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(p_bytes); @*/
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(q_bytes); @*/
  if (result == 0) {
    *p = 11;  // does this have undefined behaviour?
    //CN_VIP printf("x=%d y=%d *p=%d *q=%d\n",x,y,*p,*q);
  }
}
