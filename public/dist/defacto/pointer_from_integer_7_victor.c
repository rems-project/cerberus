#include <stdio.h>
#include <stdint.h>
void f(uintptr_t ix) {
  int y=0;
  uintptr_t iy;
    iy = ix - 0x30;  // for O0   - prints y=1
  //iy = ix - 0x20;   // for O2   - prints y=0
  int *py = (int*)iy;
  *py=1;
  printf("&y=%p  iy=0x%lx  equal=%s  ",(void*)&y,iy,(((uintptr_t)&y)==iy)?"true":"false");
  printf("y=%d\n",y); 
}
int main() {
  int x=0;
  f((uintptr_t)&x); 
}
