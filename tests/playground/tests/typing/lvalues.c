#include "stdio.h"

int main (void) {
  int a, b;
  /* GCC says: not an lvalue!
  (0 ? a : b) = 1;
  */
  int *p = (0 ? a : b);
  *p = 1;
  printf ("a: %d, b: %d\n", a, b);
  return 0;
}
