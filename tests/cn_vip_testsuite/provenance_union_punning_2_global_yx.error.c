//CN_VIP #include <stdio.h>
#include <string.h>
#include <inttypes.h>
int y=2, x=1;
typedef union { uintptr_t ui; int *p; } un;
int main() {
  un u;
  int *px = &x;
  uintptr_t i = (uintptr_t)px;
  i = i + sizeof(int);
  u.ui = i;
  int *p = u.p;
  int *q = &y;
  //CN_VIP printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11;  // does this have undefined behaviour?
    //CN_VIP printf("x=%d y=%d *p=%d *q=%d\n",x,y,*p,*q);
  }
  return 0;
}
