#include <stdint.h> 
int x=1;
int main() {
  int *p = &x;                             // assume allocated at 0x6009b8
  uintptr_t i1 = (intptr_t)p;              // value 0x6009b8 provanance x
  uintptr_t i2 = i1 & 0x00000000FFFFFFFF;  // 
  uintptr_t i3 = i2 & 0xFFFFFFFF00000000;  // value 0x0,     provenance x
  uintptr_t i4 = i3 + 0x6009b8;            // value 0x6009b8 provanance x
  int *q = (int *)i4;
  *q = 11;  // does this have defined behaviour?
  return 0;
}
