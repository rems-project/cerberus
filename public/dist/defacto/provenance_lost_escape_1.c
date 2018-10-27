#include <stdio.h>
#include <string.h> 
#include <stdint.h> 
int x=1; // assume allocated at 0x6009b8, allocation ID @1
int main() {
  int *p = &x;                      
  uintptr_t i1 = (intptr_t)p;             // (@1,0x6009b8)
  uintptr_t i2 = i1 & 0x00000000FFFFFFFF; // 
  uintptr_t i3 = i2 & 0xFFFFFFFF00000000; // (@1,0x0)
  uintptr_t i4 = i3 + 0x6009b8;           // (@1,0x6009b8)
  int *q = (int *)i4;
  printf("Addresses: p=%p\n",(void*)p);
  if (memcmp(&i1, &i4, sizeof(i1)) == 0) {
    *q = 11;  // does this have defined behaviour?
    printf("x=%d *p=%d *q=%d\n",x,*p,*q);
  }
}
