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
  /*CN_VIP*//*@ to_bytes Owned<int*>(&p); @*/
  /*CN_VIP*//*@ to_bytes Owned<int*>(&q); @*/
  /*CN_VIP*/int result = _memcmp((unsigned char*)&p, (unsigned char*)&q, sizeof(p));
  /*CN_VIP*//*@ from_bytes Owned<int*>(&p); @*/
  /*CN_VIP*//*@ from_bytes Owned<int*>(&q); @*/
#ifdef NO_ROUND_TRIP
  /*CN_VIP*/p = copy_alloc_id((uintptr_t)p, &x);
  /*CN_VIP*/q = copy_alloc_id((uintptr_t)q, &y);
#endif
  if (result == 0) {
#ifdef ANNOT
    int *r = copy_alloc_id(i, q); // CN VIP UB if ¬NO_ROUND_TRIP & ANNOT
# else
    int *r = (int *)i;
#ifdef NO_ROUND_TRIP
    /*CN_VIP*/r = copy_alloc_id((uintptr_t)r, p);
#endif
#endif
    *r=11;  // CN VIP UB if ¬ANNOT
    r=r-1;  // CN VIP UB if NO_ROUND TRIP && ANNOT
    *r=12;
    //CN_VIP printf("x=%d y=%d *q=%d *r=%d\n",x,y,*q,*r);
  }
}

/* NOTE: see tests/pvni_testsuite for why what
   vip_artifact/evaluation_cerberus/results.pdf expects for this test is probably
   wrong. */
