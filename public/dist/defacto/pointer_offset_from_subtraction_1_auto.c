#include <stdio.h>
#include <string.h> 
#include <stdint.h>
#include <inttypes.h>
int main() {
  int  x = 1, y = 2;
  intptr_t ux = (intptr_t)&x;
  intptr_t uy = (intptr_t)&y;
  intptr_t offset = uy - ux;
  printf("Addresses: &x=%"PRIiPTR" &y=%"PRIiPTR\
         " offset=%"PRIiPTR" \n",ux,uy,offset);
  int *p = (int *)(ux + offset);
  int *q = &y;
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11; // is this free of undefined behaviour?
    printf("x=%d  y=%d  *p=%d  *q=%d\n",x,y,*p,*q); 
  }
}
