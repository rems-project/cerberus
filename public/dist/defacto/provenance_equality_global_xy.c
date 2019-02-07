#include <stdio.h>
#include <stdint.h>
#include <string.h> 
int x=1, y=2;
int main() {
  int *p = &x + 1;
  int *q = &y;
  printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  _Bool b = (p==q);
  // can this be false even with identical addresses?
  __BMC_ASSUME ((intptr_t)p == (intptr_t)q && p!=q);
  printf("(p==q) = %s\n", b?"true":"false");
  return 0;
}
