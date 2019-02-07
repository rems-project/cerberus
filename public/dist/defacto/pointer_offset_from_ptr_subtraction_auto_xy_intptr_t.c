#include <stdio.h>
#include <stdint.h>
#include <string.h> 
#include <stddef.h>
int main() {
  int x=1, y=2;
  int *p = &x;
  int *q = &y;
  ptrdiff_t offset = q - p;
  int *r = p + offset;
  if ((intptr_t)r == (intptr_t)q) {
    *r = 11; // is this free of UB?
    printf("y=%d *q=%d *r=%d\n",y,*q,*r); 
  }
}
