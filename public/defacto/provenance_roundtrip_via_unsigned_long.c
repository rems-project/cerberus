#include <stdio.h>
int  x=1;
int main() {
  int *p = &x;
  unsigned long i = (unsigned long)p;
  int *q = (int *)i;
  *q = 11; // is this free of undefined behaviour?
  printf("*p=%d  *q=%d\n",*p,*q);  
}
