#include <stdio.h>
#include <string.h> 
#include <inttypes.h>
int x=1;
typedef union { uintptr_t ui; int *p; } un;
int main() {
  un u; 
  int *px = &x;
  uintptr_t i = (uintptr_t)px;
  u.ui = i;
  int *p = u.p;
  printf("Addresses: p=%p &x=%p\n",(void*)p,(void*)&x);
  *p = 11;  // is this free of undefined behaviour?
  printf("x=%d *p=%d\n",x,*p);
  return 0;
}

