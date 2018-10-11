#include <stdio.h>
#include <stdint.h>
void f(int *p) {
  static int i=0;
  *p=1;
  // printf("p=%p  &j=%p  ",(void*)p,(void*)&j);
  printf("i=%d\n",i); 
}
int main() {
  uintptr_t j = 0x60103cULL; // suppose this is the address of i
  //uintptr_t j = 0x601024ULL; // suppose this is the address of i
  int *q = (int*)j;
  f(q);
}
