#include <stdio.h>
#include <stdint.h>
void f(uintptr_t i) {
  int *p = (int*) i;
  *p=1;
}
int main() {
  static int j=0;
  int *p=&j;
  f(0x601024ULL); // suppose this is the address of j
  // printf("&j=%p  ",(void*)&j);
  // printf("p=%p  ",(void*)p);
  printf("j=%d\n",j); 
}
