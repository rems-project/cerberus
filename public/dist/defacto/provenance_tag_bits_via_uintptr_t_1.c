#include <assert.h>
#include <stdio.h>
#include <stdint.h>
int x=1;
int main() {
  int *p = &x;
  // cast &x to an integer 
  uintptr_t i = (uintptr_t) p;
  // check the bottom two bits of an int* are not used
  assert(_Alignof(int) >= 4);
  assert((i & 3u) == 0u);
  // construct an integer like &x with low-order bit set
  i = i | 1u;  
  // cast back to a pointer
  int *q = (int *) i; // does this have defined behaviour?
  // cast to integer and mask out the low-order two bits
  uintptr_t j = ((uintptr_t)q) & ~((uintptr_t)3u);  
  // cast back to a pointer
  int *r = (int *) j; 
  // are r and p now equivalent?  
  *r = 11;           //  does this have defined behaviour? 
  _Bool b = (r==p);  //  is this true?
  printf("x=%i *r=%i (r==p)=%s\n",x,*r,b?"true":"false");  
}
