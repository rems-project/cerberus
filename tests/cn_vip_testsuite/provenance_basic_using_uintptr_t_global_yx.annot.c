#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int y=2, x=1;
int main()
/*CN_VIP*//*@ accesses x; accesses y; requires x == 1i32; @*/
{
  uintptr_t ux = (uintptr_t)&x;
  uintptr_t uy = (uintptr_t)&y;
  uintptr_t offset = 4;
  ux = ux + offset;
#if defined(ANNOT)
  int *p = copy_alloc_id(ux, &y);
#else
  int *p = (int *)ux; // does this have undefined behaviour?
#endif
  int *q = &y;
  //CN_VIP printf("Addresses: &x=%p p=%p &y=%"PRIxPTR\
         "\n",(void*)&x,(void*)p,(unsigned long)uy);
  /*CN_VIP*/unsigned char* p_bytes = owned_int_ptr_to_owned_uchar_arr(&p);
  /*CN_VIP*/unsigned char* q_bytes = owned_int_ptr_to_owned_uchar_arr(&q);
  /*CN_VIP*/int result = _memcmp(p_bytes, q_bytes, sizeof(p));
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(p_bytes); @*/
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(q_bytes); @*/
  if (result == 0) {
    *p = 11; // does this have undefined behaviour?
    /*CN_VIP*//*@ assert(x == 1i32 && y == 11i32 && *p == 11i32 && *q == 11i32); @*/
    //CN_VIP printf("x=%d  y=%d  *p=%d  *q=%d\n",x,y,*p,*q);
  }
}
