#include <stdio.h>
int main() {
  // assume here that int has no trap representations and 
  // that printing an unspecified value is not itself 
  // undefined behaviour
  int i;
  int *p = &i;
  // can the following print different values?
  printf("i=0x%x\n",i);
  printf("i=0x%x\n",i);
  printf("i=0x%x\n",i);
  printf("i=0x%x\n",i);
}
