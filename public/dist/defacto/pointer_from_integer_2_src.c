// setarch `uname -m` -R $SHELL. That spawns a shell with ASLR
// disabled, and any command you run from that shell will also have ASLR
// disabled.
#include <stdio.h>
#include <stdint.h>
void f() {
  uintptr_t i=0x7fffffffdd8c; // suppose this is the address of j
  int *p = (int*)i;
  *p=1;
}
int main() {
  int j=0;
  f();
  // printf("&j=%p\n",(void*)&j);
  printf("j=%d\n",j); 
}
