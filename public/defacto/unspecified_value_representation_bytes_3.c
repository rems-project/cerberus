#include <stdio.h>
int main() {
  // assume here that the implementation-defined
  // representation of int has no trap representations
  int i;
  // printf("i=0x%x\n",i);
  // printf("i=0x%x\n",i);
  * (((unsigned char*)(&i))+1) = 0x22;
  // does i now hold an unspecified value?
  printf("i=0x%x\n",i);
  printf("i=0x%x\n",i);
}

