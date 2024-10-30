//CN_VIP #include <stdio.h>
#include <inttypes.h>
int x=1;
int main()
/*CN_VIP*//*@ accesses x; @*/
{
  int *p = &x;
  intptr_t i = (intptr_t)p;
  /*CN_VIP*/int *q = (int *)i;
#ifdef NO_ROUND_TRIP
  /*CN_VIP*/q = __cerbvar_copy_alloc_id((uintptr_t)q, &x);
#endif
  *q = 11; // is this free of undefined behaviour?
  //CN_VIP printf("*p=%d  *q=%d\n",*p,*q);
  /*CN_VIP*//*@ assert(*p == 11i32 && *q == 11i32); @*/
}
