#include <stdio.h>
#include <string.h> 
#include <stdlib.h>
#include <stddef.h>
int main() {
  void *xp=malloc(sizeof(int)); // allocation P
  void *yp=malloc(sizeof(int)); // allocation Q
  *((int*)xp)=1;
  *((int*)yp)=2;
  ptrdiff_t offset = 32; 
    // (unsigned char*)yp - (unsigned char*)xp; 
  unsigned char *p1 = (unsigned char*)xp;// provenance P
  unsigned char *p2 = p1 + offset;         
  int *p = (int*)p2;
  int *q = (int*)yp;
  printf("Addresses: xp=%p yp=%p p=%p q=%p\n",xp,yp,(void*)p,(void*)q);
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11;  // is this free of undefined behaviour?
    printf("*xp=%d *yp=%d *p=%d *q=%d\n",
           *(int*)xp,*(int*)yp,*(int*)p,*(int*)q);
  }
  return 0;
}
