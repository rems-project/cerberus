// setarch `uname -m` -R $SHELL. That spawns a shell with ASLR
// disabled, and any command you run from that shell will also have ASLR
// disabled.
#include <stdio.h>
#include <stdint.h>
void f(int *p) {
  int j=0;
  printf("&j=%p p=%p\n",(void*)&j,(void*)p);
  if (p==&j) 
    {
      printf("equal\n");
      *p=1;
    }
  printf("j=%d\n",j); 
}
int main() {
  uintptr_t i = 0x7fffffffdd6cULL;
  //uintptr_t i = 0x7fffffffdd7cULL;
  int *p = (int*)i;
  f(p);
}
