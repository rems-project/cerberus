#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <inttypes.h>
int y[2], x[2];
int main()
/*@ accesses x; @*/
{
  /*CN_VIP*//*@ extract Owned<int>, 1u64; @*/
#ifdef ANNOT
  int *p= copy_alloc_id(
    (((uintptr_t)&(x[0])) +
    (((uintptr_t)&(y[1]))-((uintptr_t)&(y[0]))))
  ,
    &x);
#else
  int *p=(int*)(((uintptr_t)&(x[0])) +
    (((uintptr_t)&(y[1]))-((uintptr_t)&(y[0]))));
#endif
  *p = 11;  // CN VIP UB (no annot)
  //CN_VIP printf("x[1]=%d *p=%d\n",x[1],*p);
  /*CN_VIP*//*@ assert(x[1u64] == 11i32 && *p == 11i32); @*/
  return 0;
}
