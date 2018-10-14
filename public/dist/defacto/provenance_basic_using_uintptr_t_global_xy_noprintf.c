#include <inttypes.h>
#include <string.h>
int x=1, y = 2;
int main() {
  uintptr_t ux = (uintptr_t)&x;
  uintptr_t uy = (uintptr_t)&y;
  uintptr_t offset = 4;
  ux = ux + offset;
  int *p = (int *)ux; // undefined behaviour?
  int *q = &y;
  if (memcmp(&p, &q, sizeof(p)) == 0) 
    *p = 11; // undefined behaviour?
}
