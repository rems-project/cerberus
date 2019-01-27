#include <inttypes.h>

int main() {
  int x=1, y=2;
  int *p = &x + 1;
  int *q = &y;

  __BMC_ASSUME((uintptr_t)p == (uintptr_t)q);

  _Bool b = (p==q);
  /* Addresses are equal, but provenances are different.
   * b can be either 0 or 1
   * SAT
   */
  assert (b == 1);
  
  return b;
}
