#include <stdio.h>
#include <stdint.h>
void f(uintptr_t i) {
  static int j=0;
  int *q = &j;
  int *p = (int*)i;
  if (p==&j) 
    *p=1;
  //printf("i=0x%lx &j=%p  ",i,(void*)&j);
  printf("j=%d\n",j); 
}
int main() {
  uintptr_t j = 0x60103cULL; // suppose this is the address of j   (P lab)
  //uintptr_t j = 0x601024ULL; // suppose this is the address of j
  f(j);
}

