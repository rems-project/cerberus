#include <stdio.h>
int  y = 2, x=1;
int main() {
  int *p = &x, *q = &y;
  _Bool b1 = (p < q); // defined behaviour?
  _Bool b2 = (p > q); // defined behaviour?
  printf("Addresses: p=%p  q=%p\n",(void*)p,(void*)q);
  printf("(p<q) = %s  (p>q) = %s\n",
         b1?"true":"false", b2?"true":"false");
}
