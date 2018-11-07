#include <stdio.h>
#include <stdint.h>
#include "charon_concrete_addresses.h"
void f() {
  uintptr_t i=ADDR010; // suppose this is the address of j
  int *p = (int*)i;
  *p=1;
}
int main() {
  static int j=0;
  f();
  //  printf("&j=%p\n",(void*)&j);
  printf("j=%d\n",j); 
}
