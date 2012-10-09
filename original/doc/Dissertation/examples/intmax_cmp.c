#include <limits.h>

int main(void) {
  // Note: INT_MAX is the greatest integer of type int.
  int i = INT_MAX;
  return i + 1 > i;
}
