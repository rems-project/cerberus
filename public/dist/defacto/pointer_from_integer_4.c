#include <stdio.h>
#include <stdint.h>
#include "charon_concrete_addresses.h"
void f(uintptr_t i) {
  static int j=0;
  uintptr_t jp = (uintptr_t)&j;
  if (i == jp) {
    printf("equal\n");
  } else {
    printf("nonequal\n");
  }
}
int main() {
  f(ADDR012);  // suppose this is the address of j
}
