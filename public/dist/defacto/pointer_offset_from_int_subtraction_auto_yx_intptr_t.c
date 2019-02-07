#include <stdio.h>
#include <string.h> 
#include <stdint.h>
#include <inttypes.h>
int main() {
  int y=2, x=1;
  uintptr_t ux = (uintptr_t)&x;
  uintptr_t uy = (uintptr_t)&y;
  uintptr_t offset = uy - ux;
  printf("Addresses: &x=%"PRIuPTR" &y=%"PRIuPTR\
         " offset=%"PRIuPTR" \n",ux,uy,offset);
  int *p = (int *)(ux + offset);
  int *q = &y;
  __BMC_ASSUME ((intptr_t)p == (intptr_t)q);
  if ((intptr_t)p == (intptr_t)q) {
    *p = 11; // is this free of UB?
    printf("x=%d y=%d *p=%d *q=%d\n",x,y,*p,*q); 
  }
}
