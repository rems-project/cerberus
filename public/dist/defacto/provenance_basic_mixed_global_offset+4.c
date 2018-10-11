#include <stdio.h>
#include <string.h> 
#include <stdint.h>
#include <inttypes.h>
int  y = 2, x=1;
int main() {
  intptr_t ux = (intptr_t)&x;
  intptr_t uy = (intptr_t)&y;
  intptr_t offset = 4;
  printf("Addresses: &x=%"PRIiPTR" &y=%"PRIiPTR\
         "\n",ux,uy);
  int *q = &y;
  if (q != NULL) {
    int *p = (int *)(ux + offset);
    if (memcmp(&p, &q, sizeof(p)) == 0) {
      *p = 11; // does this have undefined behaviour?
      printf("x=%d  y=%d  *p=%d  *q=%d\n",x,y,*p,*q); 
    }
  }
}
