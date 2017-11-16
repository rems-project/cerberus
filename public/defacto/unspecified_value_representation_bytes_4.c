#include <stdio.h>
int main() {
  // assume here that the implementation-defined
  // representation of int has no trap representations
  int i;
  printf("i=0x%x\n",i);
  printf("i=0x%x\n",i);
  unsigned char *cp = (unsigned char*)(&i);
  *(cp+1) = 0x22;
  // does *cp now hold an unspecified value?
  printf("*cp=0x%x\n",*cp);
  printf("*cp=0x%x\n",*cp);
}
