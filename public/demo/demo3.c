#include <stdint.h>
int main(void) {
  int x,y,z;
  return (uintptr_t)&x < (uintptr_t)&x;
}