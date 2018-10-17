#include <stdio.h>
#include <string.h> 
#include <stdint.h>
int  y=2, x=1;
int main() {
  int *p = &x + 1;
  intptr_t i = (intptr_t)p;
  int *pi = (int*)i;
  int *q = &y;
  printf("Addresses: pi=%p q=%p\n",(void*)pi,(void*)q);
  if (memcmp(&pi, &q, sizeof(pi)) == 0) {
    *pi = 11;  // does this have undefined behaviour?
    printf("x=%d y=%d *pi=%d *q=%d\n",x,y,*pi,*q);
  }
  return 0;
}
