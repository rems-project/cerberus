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
  /*@ apply assert_equal((u64) ux, uy); @*/
#ifdef ANNOT
  int *p = copy_alloc_id(ux, &y);
#else
  int *p = (int *)ux; // does this have undefined behaviour?
#endif
  int *q = &y;
  //CN_VIP printf("Addresses: &x=%p p=%p &y=%"PRIxPTR\
         "\n",(void*)&x,(void*)p,(unsigned long)uy);
  /*CN_VIP*//*@ to_bytes Owned<int*>(&p); @*/
  /*CN_VIP*//*@ to_bytes Owned<int*>(&q); @*/
  /*CN_VIP*/int result = _memcmp((unsigned char*)&p, (unsigned char*)&q, sizeof(p));
  /*CN_VIP*//*@ from_bytes Owned<int*>(&p); @*/
  /*CN_VIP*//*@ from_bytes Owned<int*>(&q); @*/
#ifdef NO_ROUND_TRIP
#ifdef ANNOT
  /*CN_VIP*/p = copy_alloc_id((uintptr_t)p, &y);
#endif
  /*CN_VIP*/q = copy_alloc_id((uintptr_t)q, &y); // for *q in assertion
#endif
  if (result == 0) {
    *p = 11; // CN VIP UB (no annot)
    //CN_VIP printf("x=%d  y=%d  *p=%d  *q=%d\n",x,y,*p,*q);
    /*CN_VIP*//*@ assert(x == 1i32 && y == 11i32 && *p == 11i32 && *q == 11i32); @*/
  }
}
