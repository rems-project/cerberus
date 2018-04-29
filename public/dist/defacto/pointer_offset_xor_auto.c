#include <stdio.h>
#include <inttypes.h>
int main() {
  int x=1, y=2;
  int *p = &x;
  int *q = &y;
  uintptr_t i = (uintptr_t) p;
  uintptr_t j = (uintptr_t) q;
  uintptr_t k = i ^ j;
  uintptr_t l = k ^ i;
  int *r = (int *)l;
  // are r and q now equivalent?  
  *r = 11;     // does this have defined behaviour?             
  _Bool b = (r==q); 
  printf("x=%i y=%i *r=%i (r==p)=%s\n",x,y,*r,
         b?"true":"false");  
}
