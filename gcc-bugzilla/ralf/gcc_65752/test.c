#include <stdio.h>
#include <stdint.h>
#include <limits.h>

int main() {
  int x = 0, *p = 0;
  for (uintptr_t i = 0; ; i++) {
    if (i == (uintptr_t)&x) { p = (int*)i; break; }
  }
  *p = 15;
  printf("%d\n", x);
}