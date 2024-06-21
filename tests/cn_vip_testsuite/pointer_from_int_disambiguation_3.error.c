#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int y=2, x=1;
int main()
/*CN_VIP*//*@ accesses y; accesses x; @*/
{
  int *p = &x+1;
  int *q = &y;
  uintptr_t i = (uintptr_t)p;
  uintptr_t j = (uintptr_t)q;
  /*CN_VIP*/unsigned char* p_bytes = owned_int_ptr_to_owned_uchar_arr(&p);
  /*CN_VIP*/unsigned char* q_bytes = owned_int_ptr_to_owned_uchar_arr(&q);
  /*CN_VIP*/int result = _memcmp(p_bytes, q_bytes, sizeof(p));
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(p_bytes); @*/
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(q_bytes); @*/
  if (result == 0) {
#if defined(ANNOT)
    int *r = copy_alloc_id(i, q);
#else
    int *r = (int *)i;
#endif
    *r=11;
    r=r-1;  // is this free of UB?
    *r=12;  // and this?
    //CN_VIP printf("x=%d y=%d *q=%d *r=%d\n",x,y,*q,*r);
  }
}
