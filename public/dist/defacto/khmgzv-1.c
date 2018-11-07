#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include "charon_concrete_addresses.h"
int x=0;
int main() {
  uintptr_t b = (uintptr_t) &x;
  uintptr_t a = ADDR001;
  printf("Addresses: b=0x%" PRIXPTR " a=0x%" PRIXPTR 
         "\n",b,a);
  if (memcmp(&b, &a, sizeof(b)) == 0) {
    a = (a - b) + (2 * b - b);
    int *q = (int *) a;
    *q = 123;   // does this have undefined behaviour?
    printf("*((int*)b=%d  *q=%d\n",*((int*)b),*q);
  }
  return 0;
}
