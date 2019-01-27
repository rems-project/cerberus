#include <stdint.h>
#include <inttypes.h>
int main() {
  int x=1, y=2;
  uintptr_t ux = (uintptr_t)&x;
  uintptr_t uy = (uintptr_t)&y;
  uintptr_t offset = uy - ux;
  int *p = (int *)(ux + offset);
  int *q = &y;
  if ((uintptr_t) p == (uintptr_t) q) {
    *p = 11;
  }
}
