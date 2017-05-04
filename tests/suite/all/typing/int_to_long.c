#include <limits.h>
#include <stdio.h>

int main(void) {
  long a;
  unsigned int m = UINT_MAX;
  unsigned int n = 1;
  a = m + n;
  printf("%ld\n", a);
  return 0;
}
