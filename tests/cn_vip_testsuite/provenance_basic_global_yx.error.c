//CN_VIP #include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int y=2, x=1;
int main()
/*CN_VIP*//*@ accesses x; accesses y; @*/
{
  int *p = &x + 1;
  int *q = &y;
  //CN_VIP printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  /*CN_VIP*//*@ to_bytes Owned<int*>(&p); @*/
  /*CN_VIP*//*@ to_bytes Owned<int*>(&q); @*/
  /*CN_VIP*/int result = _memcmp((unsigned char *)&p, (unsigned char*)&q, sizeof(p));
  /*CN_VIP*//*@ from_bytes Owned<int*>(&p); @*/
  /*CN_VIP*//*@ from_bytes Owned<int*>(&q); @*/
#ifdef NO_ROUND_TRIP
  /*CN_VIP*/p = __cerbvar_copy_alloc_id((uintptr_t)p, &x);
#endif
  if (result == 0) {
    *p = 11;  // CN_VIP UB
    //CN_VIP printf("x=%d y=%d *p=%d *q=%d\n",x,y,*p,*q);
  }
}
