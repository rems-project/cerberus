#include <inttypes.h>

int main() {
  int y=2, x=1;
  int *p = &x + 1;
  int *q = &y;

  if ((uintptr_t)p == (uintptr_t)q) {
    *p = 11; // UB
  }
}
