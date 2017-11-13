#include <stdio.h>
#include <inttypes.h>
int main() {
  int x=0;
  int *px = &x;
  uintptr_t ql = (uintptr_t)px;
  ql = ql + 287343;
  ql = ql - 287343;
  int *q = (int *)ql;
  *q = 1;
  printf("x=%i  *px=%i  *q=%i\n",x,*px,*q);
}
