#include <stdio.h>
#include <string.h> 
#include <stdint.h>
#include <inttypes.h>
int y=2, x=1;
int main() {
  uintptr_t ux = (uintptr_t)&x;
  uintptr_t uy = (uintptr_t)&y;
  uintptr_t offset = 4;
  ux = ux + offset;
  int *p = (int *)ux; // does this have undefined behaviour?
  int *q = &y;
  printf("Addresses: &x=%p p=%p &y=%"PRIxPTR\
         "\n",(void*)&x,(void*)p,uy);
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11; // does this have undefined behaviour?
    printf("x=%d  y=%d  *p=%d  *q=%d\n",x,y,*p,*q); 
  }
}
