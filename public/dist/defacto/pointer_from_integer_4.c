#include <stdio.h>
#include <stdint.h>
void f(uintptr_t i) {
  static int j=0;
  // printf("&j=%p\n",(void*)&j);  
  uintptr_t jp = (uintptr_t)&j;
  if (i == jp) {
    printf("equal\n");
  } else {
    printf("nonequal\n");
  }
}
int main() {
  f(0x601024ULL);  // suppose this is the address of j  (PS-to-K: is ULL right?)
}
