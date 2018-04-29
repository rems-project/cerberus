#include <stdio.h>
int main() {
  int x[2];
  int *p = &x[0];
  //is this free of undefined behaviour?
  int *q = p + 11;
  q = q - 10;
  *q = 1;
  printf("x[1]=%i  *q=%i\n",x[1],*q);
}
