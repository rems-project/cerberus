#include <inttypes.h>

int x=1, y=2;
int main() {
  int *p = &x;
  int *q = &y;
  p = p + 1;
 
  if ((uintptr_t)p == (uintptr_t)q) {
    *p = 11; // UB
  }
}
