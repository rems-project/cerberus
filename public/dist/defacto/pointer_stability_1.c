#include <stdio.h>
#include <inttypes.h>
int main() {
  int x=1;
  uintptr_t i = (uintptr_t) &x;
  uintptr_t j = (uintptr_t) &x;
  // is this guaranteed to be true?
  _Bool b = (i==j);
  printf("(i==j)=%s\n",b?"true":"false");
  return 0;
}
