#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <inttypes.h>
int y[2], x[2];
int main()
/*@ accesses x; @*/
{
#if defined(ANNOT)
  int *p= copy_alloc_id(
    (((uintptr_t)&(x[0])) +
    (((uintptr_t)&(y[1]))-((uintptr_t)&(y[0]))))
  ,
    &x);
#else
  int *p=(int*)(((uintptr_t)&(x[0])) +
    (((uintptr_t)&(y[1]))-((uintptr_t)&(y[0]))));
#endif
  /*@ extract Owned<int>, 1u64; @*/
  *p = 11;  // is this free of undefined behaviour?
  /*CN_VIP*//*@ assert(x[1u64] == 11i32 && *p == 11i32); @*/
  //CN_VIP printf("x[1]=%d *p=%d\n",x[1],*p);
  return 0;
}
