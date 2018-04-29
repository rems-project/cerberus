#include <stdio.h>
#include <string.h> 
#include <inttypes.h>
int x=0;
int main() {
  uintptr_t b = (uintptr_t) &x;
  uintptr_t a = 0x60102C;
  printf("Addresses: b=0x%" PRIXPTR " a=0x%" PRIXPTR 
         "\n",b,a);
  if (memcmp(&b, &a, sizeof(b)) == 0) {
    int *q = (int *) a;
    *q = 123;   // does this have undefined behaviour?
    printf("*((int*)b=%d  *q=%d\n",*((int*)b),*q);
  }
  return 0;
}
