#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int y=2, x=1;
int main()
/*CN_VIP*//*@ accesses y; accesses x; requires x == 1i32; @*/
{
  int *p = &x+1;
  int *q = &y;
  uintptr_t i = (uintptr_t)p;
  uintptr_t j = (uintptr_t)q;
  /*CN_VIP*//*@ to_bytes RW<int*>(&p); @*/
  /*CN_VIP*//*@ to_bytes RW<int*>(&q); @*/
  /*CN_VIP*/int result = _memcmp((unsigned char*)&p, (unsigned char*)&q, sizeof(p));
  /*CN_VIP*//*@ from_bytes RW<int*>(&p); @*/
  /*CN_VIP*//*@ from_bytes RW<int*>(&q); @*/
#ifdef NO_ROUND_TRIP
  q = copy_alloc_id(j, &y);
#endif
  if (result == 0) {
#ifdef ANNOT
    int *r = copy_alloc_id(i, q);
#else
    int *r = (int *)i;
#endif
    *r=11;  // is this free of UB?
    /*CN_VIP*//*@ assert (x == 1i32 && y == 11i32 && *q == 11i32 && *r == 11i32); @*/
    //CN_VIP printf("x=%d y=%d *q=%d *r=%d\n",x,y,*q,*r);
  }
}
