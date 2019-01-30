#include <inttypes.h>

int main() {
  int x=1, y=2;
  int *p = &x + 1;
  int *q = &y;

  __BMC_ASSUME((uintptr_t)p != (uintptr_t)q);

  _Bool b = (p==q);
  /* Different addresses, comparison is 0 */
  if (!b) {
    assert (0);
  }
  
  return 0;
}
