#include <stdio.h>
#include <stdint.h>
#include <string.h> 
#include <stddef.h>
int y=2, x=1;
int main() {
  int *p = &x;
  int *q = &y;
  ptrdiff_t offset = q - p;
  int *r = p + offset;
  __BMC_ASSUME ((intptr_t)r == (intptr_t)q);
  if ((intptr_t)r == (intptr_t)q) {
    *r = 11; // is this free of UB?
    printf("y=%d *q=%d *r=%d\n",y,*q,*r); 
  }
}
