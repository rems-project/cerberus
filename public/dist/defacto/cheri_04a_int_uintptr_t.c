#include <stdio.h>
#include <inttypes.h>
int main() {
  int x=0;
  int *px = &x;
  uintptr_t ql = (uintptr_t)px;
  //are these two lines free of undefined behaviour?
  int *q = (int *)ql;
  *q = 1;
  printf("x=%i  *px=%i  *q=%i\n",x,*px,*q);
}
//gcc-4.8 -O2 -std=c11 -pedantic -Wall -Wextra -pthread cheri_04a_int_uintptr_t.c
// && ./a.out
//x=1  *px=1  *q=1
