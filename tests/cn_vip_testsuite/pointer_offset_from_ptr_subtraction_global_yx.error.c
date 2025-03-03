//CN_VIP #include <stdio.h>
#include <string.h>
#include <stddef.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int y=2, x=1;
int main()
/*CN_VIP*//*@ accesses x; accesses y; @*/
{
  int *p = &x;
  int *q = &y;
  ptrdiff_t offset = q - p; // CN VIP UB
  int *r = p + offset;
  /*CN_VIP*//*@ to_bytes RW<int*>(&r); @*/
  /*CN_VIP*//*@ to_bytes RW<int*>(&q); @*/
  /*CN_VIP*/int result = _memcmp((unsigned char*)&r, (unsigned char*)&q, sizeof(r));
  /*CN_VIP*//*@ from_bytes RW<int*>(&r); @*/
  /*CN_VIP*//*@ from_bytes RW<int*>(&q); @*/
#ifdef NO_ROUND_TRIP
  /*CN_VIP*/r = __cerbvar_copy_alloc_id((uintptr_t)r, &x);
#endif
  if (result == 0) {
    *r = 11; // is this free of UB?
    //CN_VIP printf("y=%d *q=%d *r=%d\n",y,*q,*r);
  }
}
