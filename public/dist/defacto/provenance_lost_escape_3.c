#include <stdio.h>
#include <string.h> 
#include <stdint.h> 
int x=1;

uintptr_t remove_provenance(uintptr_t i) {
  int x;
  uintptr_t j1 = (uintptr_t)&x;         // value &x, provenance of x
  uintptr_t j2 = j1 & 0x0;              // value 0,  provenance of x
  uintptr_t k  = i - j2;                // value i,  provenance empty
  return k;
}

int main() {
  int *p = &x;                             // 
  uintptr_t i1 = (intptr_t)p;              // value &x,  provenance x
  uintptr_t i2 = i1 & 0x00000000FFFFFFFF;  // 
  uintptr_t i3 = i2 & 0xFFFFFFFF00000000;  // value 0x0, provenance x

  uintptr_t k  = remove_provenance(i1);    // value &x,  provenance empty
  uintptr_t i4 = i3 + k;                   // value &x,  provenance x
  int *q = (int *)i4;
  printf("Addresses: p=%p\n",(void*)p);
  if (memcmp(&i1, &i4, sizeof(i1)) == 0) {
    *q = 11;  // does this have defined behaviour?
    printf("x=%d *p=%d *q=%d\n",x,*p,*q);
  }
  return 0;
}
