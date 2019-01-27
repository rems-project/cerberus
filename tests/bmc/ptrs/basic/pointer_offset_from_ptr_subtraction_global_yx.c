#include <stddef.h>
#include <inttypes.h>

int y=2, x=1;
int main() {
  int *p = &x;
  int *q = &y;
  ptrdiff_t offset = q - p; // UB here
  int *r = p + offset;
  __BMC_ASSUME((uintptr_t)r == (uintptr_t) q);
  *r = 11;
}
