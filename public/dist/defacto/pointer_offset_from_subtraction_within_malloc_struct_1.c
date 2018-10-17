#include <stdio.h>
#include <string.h> 
#include <stdlib.h>
#include <stddef.h>
typedef struct { char c; int i; } st;
int main() {
  void *a = malloc(4*sizeof(st)); // allocation P
  // initialise one member of two elements of a notional array of structs
  char *p1 = (char*)((unsigned char*)a+1*sizeof(int)+offsetof(st,c));
  int  *p3 = (int *)((unsigned char*)a+3*sizeof(int)+offsetof(st,i));
  *p1 = 'a';
  *p3 = 3;
  // calculate an unsigned char* offset between pointers to those elements
  ptrdiff_t offset=((unsigned char*)p3-offsetof(st,i)) -
                   ((unsigned char*)p1-offsetof(st,c));  // provenance ?
  // add the offset to a pointer to the first struct
  unsigned char *q1  = (unsigned char*)p1 - offsetof(st,c);// provenance P
  unsigned char *q3  = ((unsigned char*)p1 - offsetof(st,c)) + offset;     // provenance P
  // and adapt to point to the i element of the third
  unsigned char *q3i = q3 + offsetof(st,i);                // provenance P
  char *r1 = (char*)q1;
  int  *r3 = (int*)q3i;
  printf("Addresses: a=%p p3=%p r3=%p\n",a,(void*)p3,(void*)r3);
  // if that has the same representation as the pointer to the i member of the third...
  if (memcmp(&p3, &r3, sizeof(p3)) == 0) {
    // try to use it to access that
    *r3 = 33;  // is this free of undefined behaviour?
    printf("*p3=%d *r3=%d \n", *p3, *r3);
  }
  return 0;
}
