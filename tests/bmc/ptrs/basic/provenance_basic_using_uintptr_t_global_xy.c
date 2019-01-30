#include <stdint.h>
#include <inttypes.h>

int x=1, y=2;
int main() {
  uintptr_t ux = (uintptr_t)&x;
  uintptr_t uy = (uintptr_t)&y;
  uintptr_t offset = 4;
  ux = ux + offset;
  int *p = (int *)ux; // does this have undefined behaviour?
  int *q = &y;
  __BMC_ASSUME((uintptr_t)p == (uintptr_t)q);
  *p = 11; // Not UB
  assert (y == 11);
  assert (x == 1);
  return y;
}
