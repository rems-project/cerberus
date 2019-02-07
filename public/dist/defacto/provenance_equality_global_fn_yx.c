#include <stdio.h>
#include <stdint.h>
#include <string.h> 
int y=2, x=1;
void f(int* p, int* q) {
  _Bool b = (p==q);
  // can this be false even with identical addresses?
  printf("(p==q) = %s\n", b?"true":"false");
  __BMC_ASSUME ((intptr_t)p == (intptr_t)q && p!=q);
  return;
}
int main() {
  int *p = &x + 1;
  int *q = &y;
  printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  f(p,q);
  return 0;
}
