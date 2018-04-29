#include <stdio.h>
int main() {
  int x=0;
  const int *p = (const int *)&x;
  //are the next two lines free of undefined behaviour?
  int *q = (int*)p;
  *q = 1;
  printf("x=%i  *p=%i  *q=%i\n",x,*p,*q);
}
