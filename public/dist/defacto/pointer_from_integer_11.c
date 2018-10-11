#include <stdio.h>
#include <stdint.h>
void f(int *p) {
  static int j=0;
  if (p==&j) 
    *p=1;
  // printf("p=%p &j=%p  ",(void*)p,(void*)&j);
  printf("j=%d\n",j); 
}
int main() {
  uintptr_t j = 0x60103cULL; // suppose this is the address of j   (P lab)
  //uintptr_t j = 0x601024ULL; // suppose this is the address of j
  int *q = (int*)j;
  f(q);
}
