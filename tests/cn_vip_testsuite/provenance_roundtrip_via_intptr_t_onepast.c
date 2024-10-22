//CN_VIP #include <stdio.h>
#include <inttypes.h>
int x=1;
int main()
/*@
accesses
    x;

requires
    (u64)(&x) < 9223372036854775804u64;
@*/
{
  int *p = &x;
  p=p+1;
  intptr_t i = (intptr_t)p;
  /*CN_VIP*/int *q = (int *)i;
#ifdef NO_ROUND_TRIP
  /*CN_VIP*/q = __cerbvar_copy_alloc_id((uintptr_t)q, &x);
#endif
  q=q-1;
  *q = 11; // is this free of undefined behaviour?
  //CN_VIP printf("*q=%d\n",*q);
  /*CN_VIP*//*@ assert(*q == 11i32); @*/
}
