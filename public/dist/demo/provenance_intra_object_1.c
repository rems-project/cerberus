#include <stdio.h>
#include <string.h> 
typedef struct { int x; int y; } st;
int main() {
  st s = { .x=1, .y=2 };
  int *p = &s.x + 1;
  int *q = &s.y;
  printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11;  // is this free of undefined behaviour?
    printf("s.x=%d s.y=%d *p=%d *q=%d\n",s.x,s.y,*p,*q);
  }
}
