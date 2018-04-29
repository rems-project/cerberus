#include <stdint.h>
int main(void) {
  int x,y,z;
  if ((uintptr_t)&x < (uintptr_t)&y && (uintptr_t)&y < (uintptr_t)&z)
    return (uintptr_t)&x < (uintptr_t)&z;
  else
    return 22;
}