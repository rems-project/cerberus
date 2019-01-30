#include <stddef.h>
#include <inttypes.h>

int main() {
  int y=2, x=1;
  int *p = &x;
  int *q = &y;
  ptrdiff_t offset = q - p;
  int *r = p + offset;
  int *r = p + offset;
  __BMC_ASSUME((uintptr_t)r == (uintptr_t) q);
  *r = 11;
}
