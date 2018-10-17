#include <stdio.h>
#include <string.h> 
#include <stdlib.h>
#include <stddef.h>
int main() {
  void *a = malloc(4*sizeof(int)); // allocation P
  // initialise two elements of a notional array within the allocation
  int *p1 = (int*)((unsigned char*)a+1*sizeof(int));
  int *p3 = (int*)((unsigned char*)a+3*sizeof(int));
  *p1 = 1;
  *p3 = 3;
  // calculate an unsigned char* offset between pointers to those elements
  ptrdiff_t offset=(unsigned char*)p3-(unsigned char*)p1;  // provenance ?
  // add the offset to a pointer to the first
  unsigned char *q1 = (unsigned char*)p1;                  // provenance P
  unsigned char *q3 = (unsigned char*)p1 + offset;         // provenance ?
  int *r1 = (int*)q1;
  int *r3 = (int*)q3;
  printf("Addresses: a=%p p3=%p r3=%p\n",a,(void*)p3,(void*)r3);
  // if that has the same representation as the pointer to the third...
  if (memcmp(&p3, &r3, sizeof(p3)) == 0) {
    // try to use it to access that
    *r3 = 11;  // is this free of undefined behaviour?
    printf("*p1=%d *r1=%d *r3=%d \n",
           *p1, *r1, *r3);
  }
  return 0;
}
