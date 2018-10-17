#include <stdio.h>
#include <stdint.h>
void f(uintptr_t i) {
  static int j=0;
  int *p = (int*)i;
  *p=1;
  //printf("i=0x%lx &j=%p  ",i,(void*)&j);
  printf("j=%d\n",j); 
}
int main() {
  //uintptr_t j = 0x600914ULL;   // suppose this is the address of j  (gcc 8.1 O0)
  uintptr_t j = 0x600934ULL; // suppose this is the address of j  (gcc 8.1 O2)
  f(j);
}
