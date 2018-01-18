#include <stdio.h>
#include <string.h> 
#include <stdint.h>
#include <assert.h>
#include <inttypes.h>
int  w=4, z=3, y = 2, x=1;
int main() {
  intptr_t ux = (intptr_t)&x;
  intptr_t uy = (intptr_t)&y;
  intptr_t offsetxy = uy - ux;
  intptr_t uz = (intptr_t)&z;
  intptr_t uw = (intptr_t)&w;
  intptr_t offsetzw = uw - uz;
  printf("Addresses: &x=%"PRIiPTR" &y=%"PRIiPTR\
         " offsetxy=%"PRIiPTR" \n",ux,uy,offsetxy);
  printf("Addresses: &z=%"PRIiPTR" &w=%"PRIiPTR\
         " offsetzw=%"PRIiPTR" \n",uz,uw,offsetzw);
  assert(offsetzw==offsetxy);
  int *p = (int *)(ux + offsetzw);
  int *q = &y;
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11; // is this free of undefined behaviour?
    printf("x=%d  y=%d  *p=%d  *q=%d\n",x,y,*p,*q); 
  }
}
