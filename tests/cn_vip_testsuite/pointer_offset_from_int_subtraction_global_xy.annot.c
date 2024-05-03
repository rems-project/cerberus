#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
int x=1, y=2;
int main() {
  uintptr_t ux = (uintptr_t)&x;
  uintptr_t uy = (uintptr_t)&y;
  uintptr_t offset = uy - ux;
  //CN_VIP printf("Addresses: &x=%"PRIuPTR" &y=%"PRIuPTR\
         " offset=%"PRIuPTR" \n",(unsigned long)ux,(unsigned long)uy,(unsigned long)offset);
#if defined(ANNOT)
  int *p = copy_alloc_id(ux + offset, &y);
#else
  int *p = (int *)(ux + offset);
#endif
  int *q = &y;
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11; // is this free of UB?
    //CN_VIP printf("x=%d y=%d *p=%d *q=%d\n",x,y,*p,*q);
  }
}
