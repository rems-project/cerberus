// identical to pointer_from_int_7.c 
#include <assert.h>
#include <stdio.h>
#include <stdint.h>
int x=1;
int main() {
  int *p = &x;
  // cast &x to an integer 
  uintptr_t i = (uintptr_t) p;
  // check that the bottom two bits of an int* are not used
  assert(_Alignof(int) >= 4);
  assert((i & 3u) == 0u);
  // construct an integer like &x with the low-order bit set
  i = i | 1u;  
  // cast back to a pointer
  int *q = (int *) i; // does this have defined behaviour?
  // cast that to an integer and mask out the low-order two bits
  uintptr_t j = ((uintptr_t)q) & ~((uintptr_t)3u);  
  // cast back to a pointer
  int *r = (int *) j; 
  // are r and p now equivalent?  
  // For example:                                         // US
  int y = *r;     // - does this have defined behaviour?  // US
  int b = (r==p); // - does this compare true?            // US
  *r=2;                                                   // US
  int z = *p;     // - does this give 2?                  // US
  printf("y=%i (r==p)=%s z=%i\n",y,b?"true":"false",z);   // US
}
//gcc-4.8 -O2 -std=c11 -pedantic -Wall -Wextra -pthread 
//  cheri_06_mask.c && ./a.out
//y=1 (r==p)=true z=2
