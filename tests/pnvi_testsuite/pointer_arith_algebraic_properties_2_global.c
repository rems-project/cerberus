#include "refinedc.h"

#include <stdio.h>
#include <inttypes.h>
int y[2], x[2];
int main() {
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
  *p = 11;  // is this free of undefined behaviour?
  printf("x[1]=%d *p=%d\n",x[1],*p);
  return 0;
}
