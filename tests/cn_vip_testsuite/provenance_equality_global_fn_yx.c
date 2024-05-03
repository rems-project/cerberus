//CN_VIP #include <stdio.h>
#include <string.h>
int y=2, x=1;
void f(int* p, int* q) {
  _Bool b = (p==q);
  // can this be false even with identical addresses?
  //CN_VIP printf("(p==q) = %s\n", b?"true":"false");
  return;
}
int main() {
  int *p = &x + 1;
  int *q = &y;
  //CN_VIP printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  f(p,q);
  return 0;
}
