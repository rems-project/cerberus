#include <stdint.h>
int main(void) {
  int x,y;
  return (uintptr_t)&x < (uintptr_t)&y;
}