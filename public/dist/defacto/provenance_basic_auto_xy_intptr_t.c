#include <stdio.h>
#include <stdint.h>
#include <string.h>
int main() {
  int x=1, y=2;
  int *p = &x + 1;
  int *q = &y;
  printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  __BMC_ASSUME ((intptr_t)p == (intptr_t)q);
  if ((intptr_t)p == (intptr_t)q) {
    *p = 11;  // does this have undefined behaviour?
    printf("x=%d y=%d *p=%d *q=%d\n",x,y,*p,*q);
  }
}
