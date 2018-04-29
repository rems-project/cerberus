#include <stdio.h>
#include <inttypes.h>
int main() {
  int y[2], x[2];
  int *p=(int*)(((uintptr_t)&(x[0])) + 
    (((uintptr_t)&(y[1]))-((uintptr_t)&(y[0]))));
  *p = 11;  // is this free of undefined behaviour?
  printf("x[1]=%d *p=%d\n",x[1],*p);
  return 0;
}
