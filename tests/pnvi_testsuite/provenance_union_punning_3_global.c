#include <stdio.h>
#include <string.h> 
#include <inttypes.h>
int x=1;
typedef union { uintptr_t ui; int *up; } un;
int main() {
  un u; 
  int *p = &x;
  u.up = p;
  uintptr_t i = u.ui;
  int *q = (int*)i;
  *q = 11;  // does this have UB?
  printf("x=%d *p=%d *q=%d\n",x,*p,*q);
}
