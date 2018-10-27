// setarch `uname -m` -R $SHELL. That spawns a shell with ASLR
// disabled, and any command you run from that shell will also have ASLR
// disabled.
#include <stdio.h>
#include <stdint.h>
void f(uintptr_t i) {
  int j=0;
  int *p = (int*)i;
  *p=1;
  //printf("i=0x%lx &j=%p  ",i,(void*)&j);
  printf("j=%d\n",j); 
}
int main() {
  //uintptr_t j = 0x7fffffffdd64ULL; //for O0 on P laptop
  uintptr_t j = 0x7fffffffdd7cULL; //for O2 on P laptop
  f(j);
}
