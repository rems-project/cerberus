#include <stdio.h>
#include <string.h> 
#include <stdlib.h>
#include <stddef.h>
#include <assert.h>
int main() {
  // malloc a region and initialise some data within it
  void *p=malloc(2*sizeof(int));                      // allocation P
  assert(p != NULL); // pick out the interesting execution
  int *i=(int*)p;
  *(i+0)=10;
  *(i+1)=11;
  // construct some pointers to that data
  int *j0 = i+0;
  int *j1 = i+1;
  // realloc the region
  void *q=realloc(p,65536*sizeof(int));                    // allocation Q
  assert(q != NULL && q != p); // pick out the interesting execution (UB?)
  // calculate the offset between the two allocations
  ptrdiff_t offset=(unsigned char*)q-(unsigned char*)p;// does this have UB?
  // try to adapt the data pointers to new allocation by adding the offset
  int *k0 = (int*)((unsigned char *)j0 + offset);      // do these have UB?
  int *k1 = (int*)((unsigned char *)j1 + offset); 
  // and use one of those for an access
  *k0=20;                                              // does this have UB? 
  printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);  // does this have UB?
  printf("*k0=%d *k1=%d\n",*k0,*k1);
  return 0;
}
