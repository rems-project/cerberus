#include <stdio.h>
int main() {
  int x=0;
  int *px = &x;
  unsigned long ql = (unsigned long)px;
  //are these two lines free of undefined behaviour?
  int *q = (int *)ql;
  *q = 1;
  printf("x=%i  *px=%i  *q=%i\n",x,*px,*q);
}
//gcc-4.8 -O2 -std=c11 -pedantic -Wall -Wextra -pthread cheri_04b_int_unsigned_long.c
//  && ./a.out
//x=1  *px=1  *q=1
