#include <stdio.h>
#include <inttypes.h>
int x=1;
int main() {
  int *p = &x;
  p=p+1;
  intptr_t i = (intptr_t)p;
  int *q = (int *)i;
  q=q-1;
  *q = 11; // is this free of undefined behaviour?
  printf("*q=%d\n",*q);  
}
