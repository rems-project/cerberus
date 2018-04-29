#include <stdio.h>
int main() {
  // assume here that the implementation-defined 
  // representation of int has no trap representations
  int i;
  unsigned char c = * ((unsigned char*)(&i)); 
  // does c now hold an unspecified value?
  printf("i=0x%x  c=0x%x\n",i,(int)c);
  printf("i=0x%x  c=0x%x\n",i,(int)c);
}

