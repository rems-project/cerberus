//CN_VIP #include <stdio.h>
#include <inttypes.h>
int x=1;
int main() {
  int *p = &x;
  intptr_t i = (intptr_t)p;
  int *q = (int *)i;
  *q = 11; // is this free of undefined behaviour?
  //CN_VIP printf("*p=%d  *q=%d\n",*p,*q);
  /*CN_VIP*//*@ assert(*p == 11i32 && *q == 11i32); @*/
}
