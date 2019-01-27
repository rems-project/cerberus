#include <stddef.h>
#include <inttypes.h>

int main() {
  int x=1, y=2;
  int *p = &x;
  int *q = &y;
  ptrdiff_t offset = q - p; // UB here
  int *r = p + offset;
  __BMC_ASSUME((uintptr_t)r == (uintptr_t) q);
  *r = 11;
}
