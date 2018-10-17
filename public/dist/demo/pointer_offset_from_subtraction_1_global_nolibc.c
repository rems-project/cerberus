#include <stdint.h>
int  y = 2, x=1;
int main() {
  intptr_t ux = (intptr_t)&x;
  intptr_t uy = (intptr_t)&y;
  intptr_t offset = uy - ux;
  int *p = (int *)(ux + offset);
  int *q = &y;
  *p = 11; // is this free of undefined behaviour?
}
