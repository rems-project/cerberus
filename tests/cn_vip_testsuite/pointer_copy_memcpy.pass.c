//CN_VIP #include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int x=1;
int main()
/*@ accesses x; @*/
{
  int *p = &x;
  int *q;
  /*CN_VIP*//*@ to_bytes RW<int*>(&p); @*/
  /*CN_VIP*//*@ to_bytes W<int*>(&q); @*/
  memcpy((unsigned char*)&q, (unsigned char*)&p, sizeof p);
  /*CN_VIP*//*@ from_bytes RW<int*>(&p); @*/
  /*CN_VIP*//*@ from_bytes RW<int*>(&q); @*/
#ifdef NO_ROUND_TRIP
  /*CN_VIP*/p = __cerbvar_copy_alloc_id((uintptr_t)p, &x); // only for *p in assertion
  /*CN_VIP*/q = __cerbvar_copy_alloc_id((uintptr_t)q, &x);
#endif
  *q = 11; // is this free of undefined behaviour?
  //CN_VIP printf("*p=%d  *q=%d\n",*p,*q);
  /*CN_VIP*//*@ assert(*p == 11i32 && *q == 11i32); @*/
}
