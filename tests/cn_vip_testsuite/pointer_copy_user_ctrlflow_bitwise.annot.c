#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <inttypes.h>
#include <limits.h>
int x=1;
int main() {
  int *p = &x;
  uintptr_t i = (uintptr_t)p;
  int uintptr_t_width = sizeof(uintptr_t) * CHAR_BIT;
  uintptr_t bit, j;
  int k;
  j=0;
  for (k=0; k<uintptr_t_width; k++) {
    bit = (i & (((uintptr_t)1) << k)) >> k;
    if (bit == 1)
      j = j | ((uintptr_t)1 << k);
    else
      j = j;
  }
#if defined(ANNOT)
  int *q = copy_alloc_id(j, &x);
#else
  int *q = (int *)j;
#endif
  *q = 11; // is this free of undefined behaviour?
  //CN_VIP printf("*p=%d  *q=%d\n",*p,*q);
}
