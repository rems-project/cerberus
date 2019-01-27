#include <inttypes.h>
int main() {
  int  y=2, x=1;
  int *p = &x + 1;
  int *q = &y;
  //printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  __BMC_ASSUME((uintptr_t)p == (uintptr_t)q);
  _Bool b = (p == q);
  return b;
}
