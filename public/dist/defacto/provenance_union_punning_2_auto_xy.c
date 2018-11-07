#include <stdio.h>
#include <string.h> 
#include <inttypes.h>
int x=1, y=2;
typedef union { uintptr_t ui; int *p; } un;
int main() {
  un u; 
  int *px = &x;
  uintptr_t i = (uintptr_t)px;
  i = i + sizeof(int);
  u.ui = i;
  int *p = u.p;
  int *q = &y;
  printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11;  // does this have undefined behaviour?
    printf("x=%d y=%d *p=%d *q=%d\n",x,y,*p,*q);
  }
  return 0;
}
