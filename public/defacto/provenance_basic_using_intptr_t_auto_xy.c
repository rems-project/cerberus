#include <stdio.h>
#include <string.h> 
#include <stdint.h>
#include <inttypes.h>
int main() {
  int  x = 1, y = 2;
  intptr_t ux = (intptr_t)&x;
  intptr_t uy = (intptr_t)&y;
  intptr_t offset = 4;
  int *p = (int *)(ux + offset);
  int *q = &y;
  printf("Addresses: &x=%"PRIiPTR" p=%p &y=%"PRIiPTR\
         "\n",ux,(void*)p,uy);
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11; // does this have undefined behaviour?
    printf("x=%d  y=%d  *p=%d  *q=%d\n",x,y,*p,*q); 
  }
}
