#include <limits.h>

int f(int x) {
  __BMC_ASSUME(x == INT_MAX);
  x++;
  return 0;
}
