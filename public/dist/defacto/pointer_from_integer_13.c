#include <stdio.h>
#include <stdint.h>
void f() {
  uintptr_t i=0x601024ULL; // suppose this is the address of j
  int *p = (int*)i;
  *p=1;
}
int main() {
  static int j=0;
  if ((uintptr_t)&j == 0x601024ULL) 
    f();
  //  printf("&j=%p\n",(void*)&j);
  printf("j=%d\n",j); 
}
